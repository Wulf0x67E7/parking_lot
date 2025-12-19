use crate::{
    deadlock,
    parking_lot::{
        lock_bucket, lock_bucket_checked, remove_from_bucket, with_thread_data, Bucket, ThreadData,
    },
    thread_parker::{ThreadParkerT, UnparkHandleT},
    ParkResult, ParkToken, UnparkResult, UnparkToken,
};
use core::{ptr, sync::atomic::Ordering};
use std::{fmt::Debug, sync::atomic::AtomicUsize, time::Instant};

pub struct QueueToken<'a> {
    key: usize,
    bucket: Option<(bool, &'a Bucket)>,
}
impl Debug for QueueToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueueToken")
            .field("key", &self.key)
            .field("locked", &self.bucket.is_some())
            .finish()
    }
}

impl<'a> QueueToken<'a> {
    pub fn new(key: usize) -> Self {
        Self { key, bucket: None }
    }
    fn new_locked(key: usize) -> Self {
        let bucket = lock_bucket(key);
        Self {
            key,
            bucket: Some((true, bucket)),
        }
    }
    fn new_lock_checked(key: &AtomicUsize) -> Self {
        let (key, bucket) = lock_bucket_checked(key);
        Self {
            key,
            bucket: Some((true, bucket)),
        }
    }
    pub fn key(&self) -> usize {
        self.key
    }
    fn with_lock<U>(mut self, f: impl FnOnce(&QueueToken<'a>, &Bucket) -> U) -> U {
        let bucket = self
            .bucket
            .get_or_insert_with(|| (true, lock_bucket(self.key)))
            .1;
        let ret = f(&self, bucket);
        drop(self);
        ret
    }
    fn dup(&self) -> QueueToken<'a> {
        Self {
            key: self.key,
            bucket: self.bucket.map(|(_, bucket)| (false, bucket)),
        }
    }
}
impl Drop for QueueToken<'_> {
    fn drop(&mut self) {
        if let Some((true, bucket)) = self.bucket {
            // SAFETY: We are the primary holder of the lock here, as required
            unsafe { bucket.mutex.unlock() };
        }
    }
}

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
pub unsafe fn park<'a>(
    queue: QueueToken<'a>,
    park_token: impl FnOnce(QueueToken<'a>) -> Option<ParkToken>,
    validate: impl FnOnce(QueueToken<'a>) -> bool,
    before_sleep: impl FnOnce(),
    removed: impl FnOnce(QueueToken<'a>, ParkResult, bool),
    timeout: Option<Instant>,
) -> ParkResult {
    // Grab our thread data, this also ensures that the hash table exists
    with_thread_data(|thread_data| {
        // Lock the bucket for the given key
        let removed = match queue.with_lock(|queue, bucket| {
            // If the validation function fails, just return
            let Some(park_token) = park_token(queue.dup()) else {
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

            if !validate(queue.dup()) {
                let removed = remove_from_bucket(
                    queue.key(),
                    |current| ptr::eq(current, thread_data),
                    bucket,
                    |_, thread_data, last| {
                        removed(queue.dup(), ParkResult::Invalid, last);
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
        QueueToken::new_lock_checked(&thread_data.key).with_lock(|queue, bucket| {
            // Now we need to check again if we were unparked or timed out. Unlike the
            // last check this is precise because we hold the bucket lock.
            if !thread_data.parker.timed_out() {
                return ParkResult::Unparked(thread_data.unpark_token.get());
            }

            // There should be no way for our thread to have been removed from the queue
            // if we timed out.
            let removed = remove_from_bucket(
                queue.key(),
                |current| ptr::eq(current, thread_data),
                bucket,
                |_, thread_data, last| {
                    removed(queue.dup(), ParkResult::TimedOut, last);
                    thread_data
                },
            );
            debug_assert!(removed == thread_data);

            ParkResult::TimedOut
        })
    })
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
pub unsafe fn unpark_one<'a>(
    queue: QueueToken<'a>,
    callback: impl FnOnce(QueueToken<'a>, UnparkResult) -> UnparkToken,
) -> UnparkResult {
    // Lock the bucket for the given key
    let mut result = UnparkResult::default();
    match queue.with_lock(|queue, bucket| {
        remove_from_bucket(
            queue.key(),
            |_| true,
            bucket,
            |_, thread_data, last| {
                if let Some(thread_data) = thread_data.as_ref() {
                    result.unparked_threads = 1;
                    result.have_more_threads = !last;
                    result.be_fair = (*bucket.fair_timeout.get()).should_timeout();
                    let token = callback(queue.dup(), result);

                    // Set the token for the target thread
                    thread_data.unpark_token.set(token);

                    // This is a bit tricky: we first lock the ThreadParker to prevent
                    // the thread from exiting and freeing its ThreadData if its wait
                    // times out. Then we unlock the queue since we don't want to keep
                    // the queue locked while we perform a system call. Finally we wake
                    // up the parked thread.
                    Ok(thread_data.parker.unpark_lock())
                } else {
                    // No threads with a matching key were found in the bucket
                    Err(callback(queue.dup(), result))
                }
            },
        )
    }) {
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
