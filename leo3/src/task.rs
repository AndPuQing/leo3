//! Safe wrapper for Lean tasks (parallel computation).
//!
//! This module provides [`LeanTask`], a safe wrapper around Lean's task
//! objects that support parallel computation with async/await integration.
//!
//! # Thread Safety
//!
//! For cross-thread task handling, use [`TaskHandle`] which is `Send + Sync`.
//! This allows spawning tasks in one thread and retrieving results in another.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::task::{LeanTask, TaskHandle, init_task_manager, finalize_task_manager};
//! use std::thread;
//!
//! fn example<'l>(lean: Lean<'l>, closure: LeanClosure<'l>) -> LeanResult<()> {
//!     // Initialize task manager (call once at startup)
//!     init_task_manager();
//!
//!     // Spawn a task and get a thread-safe handle
//!     let handle = LeanTask::spawn(closure).into_handle();
//!
//!     // Can be sent to another thread
//!     thread::spawn(move || {
//!         leo3::with_lean(|lean| {
//!             let result = handle.get(lean);
//!             // use result...
//!         });
//!     });
//!
//!     // Clean up (call once at shutdown)
//!     finalize_task_manager();
//!     Ok(())
//! }
//! ```

use crate::closure::LeanClosure;
use crate::ffi;
use crate::instance::{LeanAny, LeanBorrowed, LeanBound};
use crate::marker::Lean;
use crate::unbound::LeanUnbound;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
use std::task::{Context, Poll};

// ============================================================================
// Task Manager Functions
// ============================================================================

/// Initialize the Lean task manager with the default number of workers.
///
/// This must be called before spawning any tasks. It is safe to call
/// multiple times, but only the first call has any effect.
pub fn init_task_manager() {
    unsafe {
        ffi::closure::lean_init_task_manager();
    }
}

/// Initialize the Lean task manager with a specific number of workers.
///
/// # Arguments
///
/// * `num_workers` - The number of worker threads to use.
pub fn init_task_manager_with(num_workers: u32) {
    unsafe {
        ffi::closure::lean_init_task_manager_using(num_workers);
    }
}

/// Finalize the Lean task manager.
///
/// This should be called before program exit to clean up task resources.
pub fn finalize_task_manager() {
    unsafe {
        ffi::closure::lean_finalize_task_manager();
    }
}

/// Check if task cancellation has been requested.
///
/// This can be called from within a task to check for cooperative cancellation.
pub fn check_canceled() -> bool {
    unsafe { ffi::closure::lean_io_check_canceled_core() }
}

// ============================================================================
// Task State
// ============================================================================

/// The state of a task.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TaskState {
    /// The task is still running.
    Running = 0,
    /// The task has completed successfully.
    Finished = 1,
    /// The task was aborted (canceled or errored).
    Aborted = 2,
}

impl From<u8> for TaskState {
    fn from(value: u8) -> Self {
        match value {
            0 => TaskState::Running,
            1 => TaskState::Finished,
            2 => TaskState::Aborted,
            _ => TaskState::Aborted, // Unknown states treated as aborted
        }
    }
}

// ============================================================================
// Task Priority
// ============================================================================

/// Task priority level.
///
/// # Lean4 Reference
/// Corresponds to `Task.Priority` in Lean4.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskPriority(pub u32);

impl TaskPriority {
    /// Default priority (0).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.Priority.default` in Lean4.
    pub const DEFAULT: Self = Self(0);

    /// High priority (tasks with lower numbers run first).
    pub const HIGH: Self = Self(0);

    /// Low priority.
    pub const LOW: Self = Self(u32::MAX);

    /// Maximum priority within the thread pool.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.Priority.max` in Lean4.
    pub const MAX: Self = Self(8);

    /// Priority for dedicated threads.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.Priority.dedicated` in Lean4.
    ///
    /// Tasks spawned with this priority get their own dedicated thread
    /// and don't contend with other tasks for threads in the thread pool.
    pub const DEDICATED: Self = Self(9);
}

impl Default for TaskPriority {
    fn default() -> Self {
        Self::DEFAULT
    }
}

// ============================================================================
// LeanTask
// ============================================================================

/// Marker type for Lean task objects.
pub struct LeanTaskType<T = LeanAny> {
    _marker: PhantomData<T>,
}

/// A safe wrapper around a Lean task (parallel computation).
///
/// `LeanTask` provides:
/// - Task spawning with priority control
/// - Blocking and non-blocking result access
/// - Task state inspection
/// - Cancellation support
/// - Async/await integration via `Future`
///
/// # Memory Management
///
/// Like other Lean objects, tasks use reference counting. The `LeanTask`
/// wrapper automatically manages reference counts through [`LeanBound`].
pub type LeanTask<'l, T = LeanAny> = LeanBound<'l, LeanTaskType<T>>;

impl<'l, T> LeanTask<'l, T> {
    // ========================================================================
    // Type Checking
    // ========================================================================

    /// Check if a Lean object is a task.
    ///
    /// Returns `true` if the object is a task, `false` otherwise.
    #[inline]
    pub fn is_task(obj: &LeanBound<'l, LeanAny>) -> bool {
        unsafe {
            let ptr = obj.as_ptr();
            !ffi::inline::lean_is_scalar(ptr) && ffi::inline::lean_is_task(ptr)
        }
    }

    /// Try to convert a `LeanBound<LeanAny>` to a `LeanTask`.
    ///
    /// Returns `Some(task)` if the object is a task, `None` otherwise.
    #[inline]
    pub fn try_from_any(obj: LeanBound<'l, LeanAny>) -> Option<Self> {
        if Self::is_task(&obj) {
            Some(obj.cast())
        } else {
            None
        }
    }

    // ========================================================================
    // Creation
    // ========================================================================

    /// Spawn a new task from a closure.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.spawn` in Lean4.
    ///
    /// The closure will be executed asynchronously in a worker thread.
    pub fn spawn(closure: LeanClosure<'l>) -> Self {
        Self::spawn_with_priority(closure, TaskPriority::DEFAULT)
    }

    /// Spawn a new task with a specific priority.
    ///
    /// Tasks with lower priority numbers are executed first.
    /// Use `TaskPriority::DEDICATED` for a dedicated thread.
    pub fn spawn_with_priority(closure: LeanClosure<'l>, priority: TaskPriority) -> Self {
        let lean = closure.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_task_spawn(closure.into_ptr(), priority.0);
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    /// Create a pure task that is already completed with a value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.pure` in Lean4.
    ///
    /// This is useful for returning a task when you already have the result.
    pub fn pure(value: LeanBound<'l, T>) -> Self {
        let lean = value.lean_token();
        unsafe {
            let ptr = ffi::closure::lean_task_pure(value.into_ptr());
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    // ========================================================================
    // Inspection
    // ========================================================================

    /// Get the current state of this task.
    ///
    /// # Lean4 Reference
    /// Corresponds to `IO.getTaskState` in Lean4.
    pub fn state(&self) -> TaskState {
        unsafe { ffi::closure::lean_io_get_task_state_core(self.as_ptr()).into() }
    }

    /// Check if this task has finished (successfully or with an error).
    ///
    /// # Lean4 Reference
    /// Corresponds to `IO.hasFinished` in Lean4.
    #[inline]
    pub fn is_finished(&self) -> bool {
        self.state() != TaskState::Running
    }

    /// Alias for `is_finished` to match Lean4 naming.
    ///
    /// # Lean4 Reference
    /// Corresponds to `IO.hasFinished` in Lean4.
    #[inline]
    #[allow(non_snake_case)]
    pub fn hasFinished(&self) -> bool {
        self.is_finished()
    }

    /// Check if this task is still running.
    #[inline]
    pub fn is_running(&self) -> bool {
        self.state() == TaskState::Running
    }

    /// Check if this task was aborted.
    #[inline]
    pub fn is_aborted(&self) -> bool {
        self.state() == TaskState::Aborted
    }

    // ========================================================================
    // Result Access
    // ========================================================================

    /// Block until the task completes and get a borrowed reference to the result.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.get` in Lean4.
    ///
    /// This blocks the current thread until the task finishes.
    pub fn get(&self) -> LeanBorrowed<'_, 'l, T> {
        unsafe {
            let result = ffi::closure::lean_task_get(self.as_ptr());
            LeanBorrowed::from_ptr(result as *const _)
        }
    }

    /// Block until the task completes and get an owned reference to the result.
    ///
    /// This consumes the task and returns an owned reference to the result.
    pub fn get_owned(self) -> LeanBound<'l, T> {
        let lean = self.lean_token();
        unsafe {
            let result = ffi::inline::lean_task_get_own(self.into_ptr());
            LeanBound::from_owned_ptr(lean, result)
        }
    }

    /// Get an owned reference to the result without consuming the task.
    ///
    /// This blocks until the task finishes and increments the reference count
    /// of the result.
    pub fn get_cloned(&self) -> LeanBound<'l, T> {
        self.get().to_owned()
    }

    // ========================================================================
    // Cancellation
    // ========================================================================

    /// Request cancellation of this task.
    ///
    /// This sets a cancellation flag. The task must cooperatively check for
    /// cancellation using [`check_canceled`].
    pub fn cancel(&self) {
        unsafe {
            ffi::closure::lean_io_cancel_core(self.as_ptr());
        }
    }

    // ========================================================================
    // Combinators
    // ========================================================================

    /// Map a function over the task result.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.map` in Lean4.
    ///
    /// Returns a new task that will apply `f` to the result of this task.
    pub fn map(self, f: LeanClosure<'l>) -> LeanTask<'l, LeanAny> {
        self.map_with_priority(f, TaskPriority::DEFAULT)
    }

    /// Map a function over the task result with a specific priority.
    pub fn map_with_priority(
        self,
        f: LeanClosure<'l>,
        priority: TaskPriority,
    ) -> LeanTask<'l, LeanAny> {
        let lean = self.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_task_map(f.into_ptr(), self.into_ptr(), priority.0, false);
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    /// Monadic bind (flat-map) over the task result.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Task.bind` in Lean4.
    ///
    /// Returns a new task that will apply `f` to the result of this task,
    /// where `f` returns another task.
    pub fn bind(self, f: LeanClosure<'l>) -> LeanTask<'l, LeanAny> {
        self.bind_with_priority(f, TaskPriority::DEFAULT, false)
    }

    /// Monadic bind with priority and sync flag.
    ///
    /// If `sync` is true, the continuation runs synchronously in the same thread.
    pub fn bind_with_priority(
        self,
        f: LeanClosure<'l>,
        priority: TaskPriority,
        sync: bool,
    ) -> LeanTask<'l, LeanAny> {
        let lean = self.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_task_bind(self.into_ptr(), f.into_ptr(), priority.0, sync);
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }

    // ========================================================================
    // Future Integration
    // ========================================================================

    /// Convert this task into a `Future` for async/await.
    ///
    /// # Note
    ///
    /// Lean's task system doesn't have native waker support, so this uses
    /// polling. The future will yield `Pending` until the task finishes,
    /// then return `Ready`.
    pub fn into_future(self) -> LeanTaskFuture<'l, T> {
        LeanTaskFuture { task: Some(self) }
    }

    /// Convert this task into a thread-safe `TaskHandle`.
    ///
    /// The handle can be sent across threads and used to retrieve the
    /// task result from any thread.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use std::thread;
    ///
    /// let task = LeanTask::spawn(closure);
    /// let handle = task.into_handle();
    ///
    /// thread::spawn(move || {
    ///     leo3::with_lean(|lean| {
    ///         let result = handle.get(lean);
    ///     });
    /// });
    /// ```
    pub fn into_handle(self) -> TaskHandle<T> {
        TaskHandle {
            inner: self.unbind_mt(),
        }
    }

    /// Get a thread-safe handle without consuming this task.
    ///
    /// Creates a new `TaskHandle` by cloning the reference.
    pub fn to_handle(&self) -> TaskHandle<T> {
        TaskHandle {
            inner: self.clone().unbind_mt(),
        }
    }

    /// Get an unbound result for cross-thread use.
    ///
    /// Blocks until the task completes, then returns the result as
    /// a thread-safe `LeanUnbound`.
    pub fn get_unbound(&self) -> LeanUnbound<T> {
        self.get().to_owned().unbind_mt()
    }
}

// ============================================================================
// Future Implementation
// ============================================================================

/// A `Future` adapter for `LeanTask`.
///
/// This allows using Lean tasks with Rust's async/await syntax.
///
/// # Note
///
/// Because Lean's task system doesn't support native wakers, this future
/// uses polling. For best results, use with an executor that supports
/// polling (like `futures::executor::block_on`) or a runtime that can
/// handle non-native futures.
pub struct LeanTaskFuture<'l, T = LeanAny> {
    task: Option<LeanTask<'l, T>>,
}

impl<'l, T> Future for LeanTaskFuture<'l, T> {
    type Output = LeanBound<'l, T>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let task = self.task.as_ref().expect("Future polled after completion");

        if task.is_finished() {
            // Task is done - take ownership and return the result
            let task = self.task.take().unwrap();
            Poll::Ready(task.get_owned())
        } else {
            // Task still running - schedule a wake-up
            // Since Lean doesn't have native waker support, we just wake immediately
            // This is inefficient but correct. A proper implementation would use
            // a background thread to poll and wake when done.
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

// ============================================================================
// TaskHandle - Thread-Safe Task Reference
// ============================================================================

/// A thread-safe handle to a Lean task.
///
/// Unlike [`LeanTask`], `TaskHandle` is `Send + Sync` and can be passed
/// between threads. This is useful for:
///
/// - Spawning tasks in one thread and retrieving results in another
/// - Storing task references in concurrent data structures
/// - Building work-stealing or task-pool patterns
///
/// # Example
///
/// ```rust,ignore
/// use leo3::task::TaskHandle;
/// use std::thread;
///
/// // Spawn a task and get a handle
/// let handle: TaskHandle<LeanAny> = task.into_handle();
///
/// // Move to another thread
/// let join_handle = thread::spawn(move || {
///     // Initialize thread for Lean (if not already done)
///     leo3::prepare_freethreaded_lean();
///
///     leo3::with_lean(|lean| {
///         // Get the result in this thread
///         let result = handle.get(lean);
///         // use result...
///     });
/// });
///
/// join_handle.join().unwrap();
/// ```
pub struct TaskHandle<T = LeanAny> {
    inner: LeanUnbound<LeanTaskType<T>>,
}

// SAFETY: TaskHandle wraps LeanUnbound which is already Send + Sync
// and guarantees MT mode for atomic reference counting
unsafe impl<T: Send> Send for TaskHandle<T> {}
unsafe impl<T: Sync> Sync for TaskHandle<T> {}

impl<T> TaskHandle<T> {
    /// Create a new `TaskHandle` from an unbound task.
    ///
    /// The task must already be marked for MT use (via `unbind_mt()`).
    pub fn from_unbound(task: LeanUnbound<LeanTaskType<T>>) -> Self {
        Self { inner: task }
    }

    /// Bind this handle to a `Lean<'l>` lifetime and get a `LeanTask`.
    ///
    /// This creates a bound reference for use within a Lean scope.
    pub fn bind<'l>(&self, lean: Lean<'l>) -> LeanTask<'l, T> {
        self.inner.bind(lean)
    }

    /// Consume this handle and bind it to a `Lean<'l>` lifetime.
    pub fn into_task<'l>(self, lean: Lean<'l>) -> LeanTask<'l, T> {
        self.inner.into_bound(lean)
    }

    /// Get the current state of this task.
    ///
    /// This can be called without a `Lean` token since it only reads
    /// atomic state from the task object.
    pub fn state(&self) -> TaskState {
        unsafe { ffi::closure::lean_io_get_task_state_core(self.inner.as_ptr()).into() }
    }

    /// Check if this task has finished.
    #[inline]
    pub fn is_finished(&self) -> bool {
        self.state() != TaskState::Running
    }

    /// Check if this task is still running.
    #[inline]
    pub fn is_running(&self) -> bool {
        self.state() == TaskState::Running
    }

    /// Check if this task was aborted.
    #[inline]
    pub fn is_aborted(&self) -> bool {
        self.state() == TaskState::Aborted
    }

    /// Request cancellation of this task.
    ///
    /// This sets a cancellation flag. The task must cooperatively check
    /// for cancellation using [`check_canceled`].
    pub fn cancel(&self) {
        unsafe {
            ffi::closure::lean_io_cancel_core(self.inner.as_ptr());
        }
    }

    /// Block until the task completes and get the result.
    ///
    /// Returns a `LeanBound` tied to the provided `Lean` lifetime.
    pub fn get<'l>(&self, lean: Lean<'l>) -> LeanBound<'l, T> {
        let task = self.bind(lean);
        task.get_cloned()
    }

    /// Block until the task completes and get an unbound result.
    ///
    /// Returns a `LeanUnbound` that can be used across threads.
    pub fn get_unbound(&self) -> LeanUnbound<T> {
        unsafe {
            // We need to get the result without a Lean token
            // This is safe because:
            // 1. The task is MT-marked
            // 2. lean_task_get blocks until completion
            // 3. We immediately mark the result as MT
            let result = ffi::closure::lean_task_get(self.inner.as_ptr()) as *mut ffi::lean_object;
            ffi::object::lean_inc(result);
            LeanUnbound::from_owned_ptr(result)
        }
    }

    /// Clone this handle (increments reference count).
    #[inline]
    pub fn clone_ref(&self) -> Self {
        Self {
            inner: self.inner.clone_ref(),
        }
    }

    /// Check if this and another handle refer to the same task.
    #[inline]
    pub fn is<U>(&self, other: &TaskHandle<U>) -> bool {
        self.inner.is(&other.inner)
    }

    /// Get the raw pointer to the underlying task object.
    #[inline]
    pub fn as_ptr(&self) -> *mut ffi::lean_object {
        self.inner.as_ptr()
    }
}

impl<T> Clone for TaskHandle<T> {
    fn clone(&self) -> Self {
        self.clone_ref()
    }
}

impl<T> std::fmt::Debug for TaskHandle<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TaskHandle")
            .field("state", &self.state())
            .field("ptr", &self.inner.as_ptr())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_task_type_size() {
        // LeanTask should be pointer-sized (same as LeanBound)
        assert_eq!(
            std::mem::size_of::<LeanTask<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_task_state_conversion() {
        assert_eq!(TaskState::from(0), TaskState::Running);
        assert_eq!(TaskState::from(1), TaskState::Finished);
        assert_eq!(TaskState::from(2), TaskState::Aborted);
        assert_eq!(TaskState::from(255), TaskState::Aborted);
    }
}
