//! Optional Tokio integration for Lean tasks.
//!
//! This module provides bridges between Lean's task system and Tokio,
//! allowing Lean tasks to be awaited in Tokio runtimes without busy-polling.
//!
//! Enable with the `tokio` feature flag.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::task::TaskHandle;
//! use leo3::tokio_bridge::lean_block_in_place;
//!
//! // Convert a TaskHandle into a Tokio-compatible future
//! let handle: TaskHandle = /* ... */;
//! let result = handle.into_tokio_future().await;
//!
//! // Run synchronous Lean operations without blocking the Tokio runtime
//! lean_block_in_place(|| {
//!     // synchronous Lean work here
//! });
//! ```

use crate::closure::LeanClosure;
use crate::instance::LeanAny;
use crate::task::{LeanTask, TaskHandle};
use crate::unbound::LeanUnbound;

impl<'l> LeanTask<'l, LeanAny> {
    /// Spawn a Lean task and return a `tokio::task::JoinHandle` that resolves
    /// when the Lean task completes.
    ///
    /// Internally, a background thread waits for the Lean task to finish and
    /// sends the result through a `tokio::sync::oneshot` channel, so the Tokio
    /// runtime is never blocked.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let join_handle = LeanTask::spawn_on_tokio(closure);
    /// let result: LeanUnbound<LeanAny> = join_handle.await.unwrap();
    /// ```
    pub fn spawn_on_tokio(
        closure: LeanClosure<'l>,
    ) -> ::tokio::task::JoinHandle<LeanUnbound<LeanAny>> {
        let handle = LeanTask::spawn(closure).into_handle();
        let (tx, rx) = ::tokio::sync::oneshot::channel();

        std::thread::Builder::new()
            .name("lean-tokio-bridge".into())
            .spawn(move || {
                let result = handle.get_unbound();
                let _ = tx.send(result);
            })
            .expect("failed to spawn lean-tokio-bridge thread");

        ::tokio::task::spawn(async move { rx.await.expect("lean-tokio-bridge sender dropped") })
    }
}

impl<T: Send + 'static> TaskHandle<T> {
    /// Convert this handle into a future compatible with Tokio runtimes.
    ///
    /// A background thread waits for the Lean task to complete and sends the
    /// result through a `tokio::sync::oneshot` channel, avoiding busy-polling
    /// on the Tokio executor.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let handle: TaskHandle<LeanAny> = task.into_handle();
    /// let result: LeanUnbound<LeanAny> = handle.into_tokio_future().await;
    /// ```
    pub fn into_tokio_future(
        self,
    ) -> impl std::future::Future<Output = LeanUnbound<T>> + Send + 'static {
        let (tx, rx) = ::tokio::sync::oneshot::channel();

        std::thread::Builder::new()
            .name("lean-tokio-bridge".into())
            .spawn(move || {
                let result = self.get_unbound();
                let _ = tx.send(result);
            })
            .expect("failed to spawn lean-tokio-bridge thread");

        async move { rx.await.expect("lean-tokio-bridge sender dropped") }
    }
}

/// Run a synchronous closure within a Tokio context without blocking the
/// runtime's worker threads.
///
/// This is a thin wrapper around [`tokio::task::block_in_place`] for running
/// synchronous Lean FFI operations (e.g., `TaskHandle::get`, environment
/// queries) from within an async Tokio task.
///
/// # Panics
///
/// Panics if called from outside a Tokio multi-thread runtime context
/// (same as `tokio::task::block_in_place`).
///
/// # Example
///
/// ```rust,ignore
/// use leo3::tokio_bridge::lean_block_in_place;
///
/// let result = lean_block_in_place(|| {
///     handle.get_unbound()
/// });
/// ```
pub fn lean_block_in_place<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    ::tokio::task::block_in_place(f)
}
