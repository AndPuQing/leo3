//! Async combinators for Lean tasks.
//!
//! This module provides higher-level combinators built on top of [`LeanTask`]:
//!
//! - [`join`] / [`JoinFuture`] — Await two tasks, returning both results as a tuple
//! - [`select`] / [`SelectFuture`] — Return whichever of two tasks finishes first
//! - [`race`] / [`RaceFuture`] — Return the first result from a vec of same-typed tasks
//! - [`timeout`] / [`TimeoutFuture`] — Wrap a task with a deadline
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::task::LeanTask;
//! use std::time::Duration;
//!
//! leo3::with_lean(|lean| {
//!     let task_a = LeanTask::pure(LeanNat::from_usize(lean, 1).unwrap());
//!     let task_b = LeanTask::pure(LeanNat::from_usize(lean, 2).unwrap());
//!
//!     // Blocking: wait for both
//!     let (a, b) = join(task_a, task_b);
//!
//!     // Or with a timeout
//!     let task = LeanTask::pure(LeanNat::from_usize(lean, 42).unwrap());
//!     match timeout(task, Duration::from_secs(5)) {
//!         Ok(result) => { /* task completed in time */ }
//!         Err(e) => { /* timed out */ }
//!     }
//! });
//! ```

use crate::instance::{LeanAny, LeanBound};
use crate::task::{LeanTask, LeanTaskFuture};
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

// ============================================================================
// Error Types
// ============================================================================

/// Error returned when a task exceeds its timeout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeoutError {
    /// The duration that was exceeded.
    pub duration: Duration,
}

impl fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "task timed out after {:?}", self.duration)
    }
}

impl std::error::Error for TimeoutError {}

// ============================================================================
// Either — used by select
// ============================================================================

/// Result of a [`select`] operation, indicating which of two tasks completed first.
#[derive(Debug)]
pub enum Either<A, B> {
    /// The first (left) task completed first.
    Left(A),
    /// The second (right) task completed first.
    Right(B),
}
// ============================================================================
// join — Await two tasks, return both results
// ============================================================================

/// Block until both tasks complete, returning their results as a tuple.
pub fn join<'l, A, B>(
    task_a: LeanTask<'l, A>,
    task_b: LeanTask<'l, B>,
) -> (LeanBound<'l, A>, LeanBound<'l, B>) {
    // Simply block on both sequentially — Lean tasks run in parallel regardless
    let a = task_a.get_owned();
    let b = task_b.get_owned();
    (a, b)
}

/// A `Future` that resolves when both tasks complete, yielding a tuple of results.
pub struct JoinFuture<'l, A = LeanAny, B = LeanAny> {
    left: Option<LeanTaskFuture<'l, A>>,
    right: Option<LeanTaskFuture<'l, B>>,
    left_result: Option<LeanBound<'l, A>>,
    right_result: Option<LeanBound<'l, B>>,
}

/// Create a [`JoinFuture`] from two tasks.
pub fn join_future<'l, A, B>(
    task_a: LeanTask<'l, A>,
    task_b: LeanTask<'l, B>,
) -> JoinFuture<'l, A, B> {
    JoinFuture {
        left: Some(task_a.into_future()),
        right: Some(task_b.into_future()),
        left_result: None,
        right_result: None,
    }
}

impl<'l, A, B> Future for JoinFuture<'l, A, B> {
    type Output = (LeanBound<'l, A>, LeanBound<'l, B>);

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: we never move the inner futures after pinning
        let this = unsafe { self.get_unchecked_mut() };

        // Poll left if not yet resolved
        if this.left_result.is_none() {
            if let Some(fut) = this.left.as_mut() {
                match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                    Poll::Ready(val) => {
                        this.left_result = Some(val);
                        this.left = None;
                    }
                    Poll::Pending => {}
                }
            }
        }

        // Poll right if not yet resolved
        if this.right_result.is_none() {
            if let Some(fut) = this.right.as_mut() {
                match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                    Poll::Ready(val) => {
                        this.right_result = Some(val);
                        this.right = None;
                    }
                    Poll::Pending => {}
                }
            }
        }

        if this.left_result.is_some() && this.right_result.is_some() {
            Poll::Ready((
                this.left_result.take().unwrap(),
                this.right_result.take().unwrap(),
            ))
        } else {
            Poll::Pending
        }
    }
}

// ============================================================================
// select — Return whichever of two tasks finishes first
// ============================================================================

/// Block until one of two tasks completes, returning the winner and cancelling the loser.
///
/// The losing task is cancelled via cooperative cancellation.
pub fn select<'l, A, B>(
    task_a: LeanTask<'l, A>,
    task_b: LeanTask<'l, B>,
) -> Either<LeanBound<'l, A>, LeanBound<'l, B>> {
    // Poll states until one finishes
    loop {
        if task_a.is_finished() {
            task_b.cancel();
            return Either::Left(task_a.get_owned());
        }
        if task_b.is_finished() {
            task_a.cancel();
            return Either::Right(task_b.get_owned());
        }
        std::thread::sleep(Duration::from_micros(100));
    }
}

/// A `Future` that resolves when either task completes, cancelling the other.
pub struct SelectFuture<'l, A = LeanAny, B = LeanAny> {
    left: Option<LeanTask<'l, A>>,
    right: Option<LeanTask<'l, B>>,
    left_future: Option<LeanTaskFuture<'l, A>>,
    right_future: Option<LeanTaskFuture<'l, B>>,
}

/// Create a [`SelectFuture`] from two tasks.
pub fn select_future<'l, A, B>(
    task_a: LeanTask<'l, A>,
    task_b: LeanTask<'l, B>,
) -> SelectFuture<'l, A, B> {
    // We need to keep references to cancel the loser, so clone before converting
    let left_handle = task_a.clone();
    let right_handle = task_b.clone();
    SelectFuture {
        left: Some(left_handle),
        right: Some(right_handle),
        left_future: Some(task_a.into_future()),
        right_future: Some(task_b.into_future()),
    }
}

impl<'l, A, B> Future for SelectFuture<'l, A, B> {
    type Output = Either<LeanBound<'l, A>, LeanBound<'l, B>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        // Try left
        if let Some(fut) = this.left_future.as_mut() {
            match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                Poll::Ready(val) => {
                    this.left_future = None;
                    this.left = None;
                    // Cancel the right task
                    if let Some(right) = this.right.take() {
                        right.cancel();
                    }
                    this.right_future = None;
                    return Poll::Ready(Either::Left(val));
                }
                Poll::Pending => {}
            }
        }

        // Try right
        if let Some(fut) = this.right_future.as_mut() {
            match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                Poll::Ready(val) => {
                    this.right_future = None;
                    this.right = None;
                    // Cancel the left task
                    if let Some(left) = this.left.take() {
                        left.cancel();
                    }
                    this.left_future = None;
                    return Poll::Ready(Either::Right(val));
                }
                Poll::Pending => {}
            }
        }

        Poll::Pending
    }
}

// ============================================================================
// race — First result from a vec of same-typed tasks
// ============================================================================

/// Block until one of the tasks completes, returning its result and cancelling the rest.
///
/// # Panics
///
/// Panics if `tasks` is empty.
pub fn race<'l, T>(tasks: Vec<LeanTask<'l, T>>) -> LeanBound<'l, T> {
    assert!(!tasks.is_empty(), "race requires at least one task");

    loop {
        for (i, task) in tasks.iter().enumerate() {
            if task.is_finished() {
                // Cancel all other tasks
                for (j, other) in tasks.iter().enumerate() {
                    if j != i {
                        other.cancel();
                    }
                }
                // We need to get the result — get_cloned since we can't move out of the vec
                return task.get_cloned();
            }
        }
        std::thread::sleep(Duration::from_micros(100));
    }
}

/// A `Future` that resolves when any task in the vec completes, cancelling the rest.
pub struct RaceFuture<'l, T = LeanAny> {
    tasks: Vec<LeanTask<'l, T>>,
    futures: Vec<Option<LeanTaskFuture<'l, T>>>,
}

/// Create a [`RaceFuture`] from a vec of tasks.
///
/// # Panics
///
/// Panics if `tasks` is empty.
pub fn race_future<'l, T>(tasks: Vec<LeanTask<'l, T>>) -> RaceFuture<'l, T> {
    assert!(!tasks.is_empty(), "race_future requires at least one task");

    // Clone tasks for cancellation, convert originals to futures
    let cancel_refs: Vec<LeanTask<'l, T>> = tasks.to_vec();
    let futures: Vec<Option<LeanTaskFuture<'l, T>>> =
        tasks.into_iter().map(|t| Some(t.into_future())).collect();

    RaceFuture {
        tasks: cancel_refs,
        futures,
    }
}

impl<'l, T> Future for RaceFuture<'l, T> {
    type Output = LeanBound<'l, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        for i in 0..this.futures.len() {
            if let Some(fut) = this.futures[i].as_mut() {
                match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                    Poll::Ready(val) => {
                        // Cancel all other tasks
                        for (j, task) in this.tasks.iter().enumerate() {
                            if j != i {
                                task.cancel();
                            }
                        }
                        // Clear all futures
                        for f in this.futures.iter_mut() {
                            *f = None;
                        }
                        return Poll::Ready(val);
                    }
                    Poll::Pending => {}
                }
            }
        }

        Poll::Pending
    }
}

// ============================================================================
// timeout — Wrap a task with a deadline
// ============================================================================

/// Block until the task completes or the timeout expires.
///
/// Returns `Ok(result)` if the task finishes in time, or `Err(TimeoutError)` if
/// the deadline is exceeded. On timeout, the task is cancelled.
pub fn timeout<'l, T>(
    task: LeanTask<'l, T>,
    duration: Duration,
) -> Result<LeanBound<'l, T>, TimeoutError> {
    let deadline = Instant::now() + duration;

    loop {
        if task.is_finished() {
            return Ok(task.get_owned());
        }
        if Instant::now() >= deadline {
            task.cancel();
            return Err(TimeoutError { duration });
        }
        // Sleep a short interval to avoid busy-spinning
        let remaining = deadline.saturating_duration_since(Instant::now());
        std::thread::sleep(remaining.min(Duration::from_millis(1)));
    }
}

/// A `Future` that resolves when the inner task completes or the timeout expires.
pub struct TimeoutFuture<'l, T = LeanAny> {
    task: Option<LeanTask<'l, T>>,
    inner: Option<LeanTaskFuture<'l, T>>,
    deadline: Instant,
    duration: Duration,
}

/// Create a [`TimeoutFuture`] wrapping a task with a deadline.
pub fn timeout_future<'l, T>(task: LeanTask<'l, T>, duration: Duration) -> TimeoutFuture<'l, T> {
    let cancel_ref = task.clone();
    TimeoutFuture {
        task: Some(cancel_ref),
        inner: Some(task.into_future()),
        deadline: Instant::now() + duration,
        duration,
    }
}

impl<'l, T> Future for TimeoutFuture<'l, T> {
    type Output = Result<LeanBound<'l, T>, TimeoutError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        // Check deadline first
        if Instant::now() >= this.deadline {
            if let Some(task) = this.task.take() {
                task.cancel();
            }
            this.inner = None;
            return Poll::Ready(Err(TimeoutError {
                duration: this.duration,
            }));
        }

        // Poll the inner future
        if let Some(fut) = this.inner.as_mut() {
            match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                Poll::Ready(val) => {
                    this.inner = None;
                    this.task = None;
                    return Poll::Ready(Ok(val));
                }
                Poll::Pending => {
                    // Schedule a wake-up near the deadline so we can check again.
                    // The inner future's waker thread will also wake us on completion.
                    cx.waker().wake_by_ref();
                }
            }
        }

        Poll::Pending
    }
}
