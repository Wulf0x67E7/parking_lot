use crate::{
    FilterOp, ParkResult, ParkToken, RequeueOp, UnparkResult, UnparkToken,
    parking_lot::{QueueToken, ThreadData, lock_bucket, lock_bucket_pair, unlock_bucket_pair},
    thread_parker::{ThreadParkerT, UnparkHandleT},
    util::UncheckedOptionExt,
};
use core::{ptr, sync::atomic::Ordering};
use smallvec::SmallVec;
use std::time::Instant;

/// Parks the current thread in the queue associated with the given key.
///
/// The `validate` function is called while the queue is locked and can abort
/// the operation by returning false. If `validate` returns true then the
/// current thread is appended to the queue and the queue is unlocked.
///
/// The `before_sleep` function is called after the queue is unlocked but before
/// the thread is put to sleep. The thread will then sleep until it is unparked
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
    key: usize,
    validate: impl FnOnce() -> bool,
    before_sleep: impl FnOnce(),
    timed_out: impl FnOnce(usize, bool),
    park_token: ParkToken,
    timeout: Option<Instant>,
) -> ParkResult {
    unsafe {
        use super::reentrant::park as park_reentrant;
        park_reentrant(
            QueueToken::new(key),
            |_| validate().then_some(park_token),
            |_| true,
            || before_sleep(),
            |queue, _, last| timed_out(queue.key(), last),
            timeout,
        )
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
    key: usize,
    callback: impl FnOnce(UnparkResult) -> UnparkToken,
) -> UnparkResult {
    use super::reentrant::unpark_one as unpark_one_reentrant;
    unsafe { unpark_one_reentrant(QueueToken::new(key), |_, result| callback(result)) }
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
pub unsafe fn unpark_all(key: usize, unpark_token: UnparkToken) -> usize {
    use super::reentrant::unpark_all as unpark_all_reentrant;
    unsafe { unpark_all_reentrant(QueueToken::new(key), |_| unpark_token) }
}

/// Removes all threads from the queue associated with `key_from`, optionally
/// unparks the first one and requeues the rest onto the queue associated with
/// `key_to`.
///
/// The `validate` function is called while both queues are locked. Its return
/// value will determine which operation is performed, or whether the operation
/// should be aborted. See `RequeueOp` for details about the different possible
/// return values.
///
/// The `callback` function is also called while both queues are locked. It is
/// passed the `RequeueOp` returned by `validate` and an `UnparkResult`
/// indicating whether a thread was unparked and whether there are threads still
/// parked in the new queue. This `UnparkResult` value is also returned by
/// `unpark_requeue`.
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
/// The `validate` and `callback` functions are called while the queue is locked
/// and must not panic or call into any function in `parking_lot`.
#[inline]
pub unsafe fn unpark_requeue(
    key_from: usize,
    key_to: usize,
    validate: impl FnOnce() -> RequeueOp,
    callback: impl FnOnce(RequeueOp, UnparkResult) -> UnparkToken,
) -> UnparkResult {
    unsafe {
        // Lock the two buckets for the given key
        let (bucket_from, bucket_to) = lock_bucket_pair(key_from, key_to);

        // If the validation function fails, just return
        let mut result = UnparkResult::default();
        let op = validate();
        if op == RequeueOp::Abort {
            // SAFETY: Both buckets are locked, as required.
            unlock_bucket_pair(bucket_from, bucket_to);
            return result;
        }

        // Remove all threads with the given key in the source bucket
        let mut link = &bucket_from.queue_head;
        let mut current = bucket_from.queue_head.get();
        let mut previous = ptr::null();
        let mut requeue_threads: *const ThreadData = ptr::null();
        let mut requeue_threads_tail: *const ThreadData = ptr::null();
        let mut wakeup_thread = None;
        while !current.is_null() {
            if (*current).key.load(Ordering::Relaxed) == key_from {
                // Remove the thread from the queue
                let next = (*current).next_in_queue.get();
                link.set(next);
                if bucket_from.queue_tail.get() == current {
                    bucket_from.queue_tail.set(previous);
                }

                // Prepare the first thread for wakeup and requeue the rest.
                if (op == RequeueOp::UnparkOneRequeueRest || op == RequeueOp::UnparkOne)
                    && wakeup_thread.is_none()
                {
                    wakeup_thread = Some(current);
                    result.unparked_threads = 1;
                } else {
                    if !requeue_threads.is_null() {
                        (*requeue_threads_tail).next_in_queue.set(current);
                    } else {
                        requeue_threads = current;
                    }
                    requeue_threads_tail = current;
                    (*current).key.store(key_to, Ordering::Relaxed);
                    result.requeued_threads += 1;
                }
                if op == RequeueOp::UnparkOne || op == RequeueOp::RequeueOne {
                    // Scan the rest of the queue to see if there are any other
                    // entries with the given key.
                    let mut scan = next;
                    while !scan.is_null() {
                        if (*scan).key.load(Ordering::Relaxed) == key_from {
                            result.have_more_threads = true;
                            break;
                        }
                        scan = (*scan).next_in_queue.get();
                    }
                    break;
                }
                current = next;
            } else {
                link = &(*current).next_in_queue;
                previous = current;
                current = link.get();
            }
        }

        // Add the requeued threads to the destination bucket
        if !requeue_threads.is_null() {
            (*requeue_threads_tail).next_in_queue.set(ptr::null());
            if !bucket_to.queue_head.get().is_null() {
                (*bucket_to.queue_tail.get())
                    .next_in_queue
                    .set(requeue_threads);
            } else {
                bucket_to.queue_head.set(requeue_threads);
            }
            bucket_to.queue_tail.set(requeue_threads_tail);
        }

        // Invoke the callback before waking up the thread
        if result.unparked_threads != 0 {
            result.be_fair = (*bucket_from.fair_timeout.get()).should_timeout();
        }
        let token = callback(op, result);

        // See comment in unpark_one for why we mess with the locking
        if let Some(wakeup_thread) = wakeup_thread {
            (*wakeup_thread).unpark_token.set(token);
            let handle = (*wakeup_thread).parker.unpark_lock();
            // SAFETY: Both buckets are locked, as required.
            unlock_bucket_pair(bucket_from, bucket_to);
            handle.unpark();
        } else {
            // SAFETY: Both buckets are locked, as required.
            unlock_bucket_pair(bucket_from, bucket_to);
        }

        result
    }
}

/// Unparks a number of threads from the front of the queue associated with
/// `key` depending on the results of a filter function which inspects the
/// `ParkToken` associated with each thread.
///
/// The `filter` function is called for each thread in the queue or until
/// `FilterOp::Stop` is returned. This function is passed the `ParkToken`
/// associated with a particular thread, which is unparked if `FilterOp::Unpark`
/// is returned.
///
/// The `callback` function is also called while both queues are locked. It is
/// passed an `UnparkResult` indicating the number of threads that were unparked
/// and whether there are still parked threads in the queue. This `UnparkResult`
/// value is also returned by `unpark_filter`.
///
/// The `callback` function should return an `UnparkToken` value which will be
/// passed to all threads that are unparked. If no thread is unparked then the
/// returned value is ignored.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `filter` and `callback` functions are called while the queue is locked
/// and must not panic or call into any function in `parking_lot`.
#[inline]
pub unsafe fn unpark_filter(
    key: usize,
    mut filter: impl FnMut(ParkToken) -> FilterOp,
    callback: impl FnOnce(UnparkResult) -> UnparkToken,
) -> UnparkResult {
    unsafe {
        // Lock the bucket for the given key
        let bucket = lock_bucket(key);

        // Go through the queue looking for threads with a matching key
        let mut link = &bucket.queue_head;
        let mut current = bucket.queue_head.get();
        let mut previous = ptr::null();
        let mut threads = SmallVec::<[_; 8]>::new();
        let mut result = UnparkResult::default();
        while !current.is_null() {
            if (*current).key.load(Ordering::Relaxed) == key {
                // Call the filter function with the thread's ParkToken
                let next = (*current).next_in_queue.get();
                match filter((*current).park_token.get()) {
                    FilterOp::Unpark => {
                        // Remove the thread from the queue
                        link.set(next);
                        if bucket.queue_tail.get() == current {
                            bucket.queue_tail.set(previous);
                        }

                        // Add the thread to our list of threads to unpark
                        threads.push((current, None));

                        current = next;
                    }
                    FilterOp::Skip => {
                        result.have_more_threads = true;
                        link = &(*current).next_in_queue;
                        previous = current;
                        current = link.get();
                    }
                    FilterOp::Stop => {
                        result.have_more_threads = true;
                        break;
                    }
                }
            } else {
                link = &(*current).next_in_queue;
                previous = current;
                current = link.get();
            }
        }

        // Invoke the callback before waking up the threads
        result.unparked_threads = threads.len();
        if result.unparked_threads != 0 {
            result.be_fair = (*bucket.fair_timeout.get()).should_timeout();
        }
        let token = callback(result);

        // Pass the token to all threads that are going to be unparked and prepare
        // them for unparking.
        for t in threads.iter_mut() {
            (*t.0).unpark_token.set(token);
            t.1 = Some((*t.0).parker.unpark_lock());
        }

        // SAFETY: We hold the lock here, as required
        bucket.mutex.unlock();

        // Now that we are outside the lock, wake up all the threads that we removed
        // from the queue.
        for (_, handle) in threads.into_iter() {
            handle.unchecked_unwrap().unpark();
        }

        result
    }
}
