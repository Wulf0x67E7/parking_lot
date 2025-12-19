use smallvec::SmallVec;

use crate::{
    ParkResult, ParkToken, UnparkResult, UnparkToken, deadlock,
    parking_lot::{BucketCursor, QueueToken, remove_from_bucket, with_thread_data},
    thread_parker::{ThreadParkerT, UnparkHandleT},
};
use core::{ptr, sync::atomic::Ordering};
use std::time::Instant;

/// Parks the current thread in the queue associated with the given key.
///
/// The `validate` function is called while the queue is locked and can abort
/// the operation by returning None. If `validate` returns Some(ParkToken) then the
/// current thread is appended to the queue.
///
/// The `before_sleep` function is called after the current thread is appended
/// to the queue but before the queue is unlocked and the thread is put to sleep.
/// The Queue is then unlocked and the thread will then sleep until it is unparked
/// or the given timeout is reached.
///
/// The `timed_out` function is also called while the queue is locked, but only
/// if the timeout was reached. It is passed the key of the queue it was in when
/// it timed out, which may be different from the original key if
/// `unpark_requeue` was called. It is also passed a bool which indicates
/// whether it was the last thread in the queue.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `validate` and `timed_out` functions are called while the queue is
/// locked and must not panic or call into any function in `parking_lot`.
///
/// The `before_sleep` function is called outside the queue lock and is allowed
/// to call `unpark_one`, `unpark_all`, `unpark_requeue` or `unpark_filter`, but
/// it is not allowed to call `park` or panic.
#[inline]
pub unsafe fn park(
    queue: QueueToken<'_>,
    park_token: impl FnOnce(&QueueToken<'_>) -> Option<ParkToken>,
    validate: impl FnOnce(&QueueToken<'_>) -> bool,
    before_sleep: impl FnOnce(),
    removed: impl FnOnce(&QueueToken<'_>, ParkResult, bool),
    timeout: Option<Instant>,
) -> ParkResult {
    unsafe {
        // Grab our thread data, this also ensures that the hash table exists
        with_thread_data(|thread_data| {
            // Lock the bucket for the given key
            let removed = match queue.with_lock(|queue, bucket| {
                // If the validation function fails, just return
                let Some(park_token) = park_token(queue) else {
                    return Err(ParkResult::Invalid);
                };

                // Append our thread data to the queue and unlock the bucket
                thread_data.parked_with_timeout.set(timeout.is_some());
                thread_data.next_in_queue.set(ptr::null());
                thread_data.key.store(queue.key, Ordering::Relaxed);
                thread_data.park_token.set(park_token);
                thread_data.parker.prepare_park();
                if !bucket.queue_head.get().is_null() {
                    (*bucket.queue_tail.get()).next_in_queue.set(thread_data);
                } else {
                    bucket.queue_head.set(thread_data);
                }
                bucket.queue_tail.set(thread_data);

                if !validate(queue) {
                    let removed = remove_from_bucket(
                        queue.dup(),
                        |current| ptr::eq(current, thread_data),
                        |_, thread_data, last| {
                            removed(queue, ParkResult::Invalid, last);
                            thread_data
                        },
                    );
                    debug_assert!(removed == thread_data);
                    return Err(ParkResult::Invalid);
                }

                Ok(removed)
            }) {
                Ok(removed) => removed,
                Err(res) => return res,
            };
            // Invoke the pre-sleep callback
            before_sleep();

            // Park our thread and determine whether we were woken up by an unpark
            // or by our timeout. Note that this isn't precise: we can still be
            // unparked since we are still in the queue.
            let unparked = match timeout {
                Some(timeout) => thread_data.parker.park_until(timeout),
                None => {
                    thread_data.parker.park();
                    // call deadlock detection on_unpark hook
                    deadlock::on_unpark(thread_data);
                    true
                }
            };

            // If we were unparked, return now
            if unparked {
                return ParkResult::Unparked(thread_data.unpark_token.get());
            }

            // Lock our bucket again. Note that the hashtable may have been rehashed in
            // the meantime. Our key may also have changed if we were requeued.
            QueueToken::new_lock_checked(&thread_data.key).with_lock(|queue, _| {
                // Now we need to check again if we were unparked or timed out. Unlike the
                // last check this is precise because we hold the bucket lock.
                if !thread_data.parker.timed_out() {
                    return ParkResult::Unparked(thread_data.unpark_token.get());
                }

                // There should be no way for our thread to have been removed from the queue
                // if we timed out.
                let removed = remove_from_bucket(
                    queue.dup(),
                    |current| ptr::eq(current, thread_data),
                    |queue, thread_data, last| {
                        removed(queue, ParkResult::TimedOut, last);
                        thread_data
                    },
                );
                debug_assert!(removed == thread_data);

                ParkResult::TimedOut
            })
        })
    }
}

/// Unparks one thread from the queue associated with the given key.
///
/// The `callback` function is called while the queue is locked and before the
/// target thread is woken up. The `UnparkResult` argument to the function
/// indicates whether a thread was found in the queue and whether this was the
/// last thread in the queue. This value is also returned by `unpark_one`.
///
/// The `callback` function should return an `UnparkToken` value which will be
/// passed to the thread that is unparked. If no thread is unparked then the
/// returned value is ignored.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `callback` function is called while the queue is locked and must not
/// panic or call into any function in `parking_lot`.
///
/// The `parking_lot` functions are not re-entrant and calling this method
/// from the context of an asynchronous signal handler may result in undefined
/// behavior, including corruption of internal state and/or deadlocks.
#[inline]
pub unsafe fn unpark_one(
    queue: QueueToken<'_>,
    callback: impl FnOnce(&QueueToken<'_>, UnparkResult) -> UnparkToken,
) -> UnparkResult {
    unsafe {
        // Lock the bucket for the given key
        let mut result = UnparkResult::default();
        match remove_from_bucket(
            queue.dup(),
            |thread_data| thread_data.key.load(Ordering::Relaxed) == queue.key(),
            |queue, thread_data, last| {
                if let Some(thread_data) = thread_data.as_ref() {
                    // Update the result
                    result.unparked_threads = 1;
                    result.have_more_threads = !last;
                    result.be_fair = queue
                        .dup()
                        .with_lock(|_, bucket| (*bucket.fair_timeout.get()).should_timeout());
                    // Set the token for the target thread
                    thread_data.unpark_token.set(callback(queue, result));
                    // This is a bit tricky: we first lock the ThreadParker to prevent
                    // the thread from exiting and freeing its ThreadData if its wait
                    // times out. Then we unlock the queue since we don't want to keep
                    // the queue locked while we perform a system call. Finally we wake
                    // up the parked thread.
                    Ok(thread_data.parker.unpark_lock())
                } else {
                    // No threads with a matching key were found in the bucket
                    Err(callback(queue, result))
                }
            },
        ) {
            Ok(handle) => {
                debug_assert_eq!(result.unparked_threads, 1);
                handle.unpark();
            }
            Err(_) => {
                debug_assert_eq!(result, UnparkResult::default());
            }
        }
        result
    }
}

/// Unparks all threads in the queue associated with the given key.
///
/// The given `UnparkToken` is passed to all unparked threads.
///
/// This function returns the number of threads that were unparked.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `parking_lot` functions are not re-entrant and calling this method
/// from the context of an asynchronous signal handler may result in undefined
/// behavior, including corruption of internal state and/or deadlocks.
#[inline]
pub unsafe fn unpark_all(
    queue: QueueToken<'_>,
    mut callback: impl FnMut(ParkToken) -> UnparkToken,
) -> usize {
    let mut threads = SmallVec::<[_; 8]>::new();
    queue.with_lock(|queue, bucket| {
        let mut cursor = BucketCursor::new(bucket);
        while let Some(thread_data) = unsafe { cursor.current() } {
            if thread_data.key.load(Ordering::Relaxed) == queue.key() {
                unsafe { cursor.remove() };
                thread_data
                    .unpark_token
                    .set(callback(thread_data.park_token.get()));
                threads.push(unsafe { thread_data.parker.unpark_lock() });
            } else {
                unsafe { cursor.next() };
            }
        }
    });
    // Now that we are outside the lock, wake up all the threads that we removed
    // from the queue.
    let num_threads = threads.len();
    for handle in threads.into_iter() {
        unsafe { handle.unpark() };
    }
    num_threads
}
