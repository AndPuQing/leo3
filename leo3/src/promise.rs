//! Safe wrapper for Lean promises (manually-resolvable async values).
//!
//! This module provides [`LeanPromise`], a safe wrapper around Lean's promise
//! objects that allow manual resolution of async computations.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::promise::LeanPromise;
//! use leo3::task::LeanTask;
//!
//! fn example<'l>(lean: Lean<'l>) -> LeanResult<()> {
//!     // Create a promise
//!     let promise = LeanPromise::new(lean);
//!
//!     // Get the associated task (can be awaited)
//!     let task = promise.task();
//!
//!     // Later, resolve the promise with a value
//!     promise.resolve(some_value);
//!
//!     // The task will now complete with the resolved value
//!     Ok(())
//! }
//! ```

use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::task::LeanTask;
use std::marker::PhantomData;

/// Marker type for Lean promise objects.
pub struct LeanPromiseType<T = LeanAny> {
    _marker: PhantomData<T>,
}

/// A safe wrapper around a Lean promise (manually-resolvable async value).
///
/// `LeanPromise` allows you to create an async computation that can be
/// resolved later with a value. This is useful for bridging synchronous
/// and asynchronous code, or for implementing custom async patterns.
///
/// # Example Flow
///
/// 1. Create a promise with [`LeanPromise::new`]
/// 2. Get the associated task with [`LeanPromise::task`]
/// 3. Pass the task to code that needs the result asynchronously
/// 4. When the value is ready, call [`LeanPromise::resolve`]
/// 5. The task automatically completes with the resolved value
///
/// # Memory Management
///
/// Like other Lean objects, promises use reference counting. The `LeanPromise`
/// wrapper automatically manages reference counts through [`LeanBound`].
///
/// # Important
///
/// - Each promise can only be resolved once
/// - Resolving consumes the promise
/// - The associated task will block until the promise is resolved
pub type LeanPromise<'l, T = LeanAny> = LeanBound<'l, LeanPromiseType<T>>;

impl<'l, T> LeanPromise<'l, T> {
    // ========================================================================
    // Type Checking
    // ========================================================================

    /// Check if a Lean object is a promise.
    ///
    /// Returns `true` if the object is a promise, `false` otherwise.
    #[inline]
    pub fn is_promise(obj: &LeanBound<'l, LeanAny>) -> bool {
        unsafe {
            let ptr = obj.as_ptr();
            !ffi::inline::lean_is_scalar(ptr) && ffi::inline::lean_is_promise(ptr)
        }
    }

    /// Try to convert a `LeanBound<LeanAny>` to a `LeanPromise`.
    ///
    /// Returns `Some(promise)` if the object is a promise, `None` otherwise.
    #[inline]
    pub fn try_from_any(obj: LeanBound<'l, LeanAny>) -> Option<Self> {
        if Self::is_promise(&obj) {
            Some(obj.cast())
        } else {
            None
        }
    }

    // ========================================================================
    // Creation
    // ========================================================================

    /// Create a new unresolved promise.
    ///
    /// The promise can be resolved later with [`resolve`](Self::resolve).
    ///
    /// # Note
    ///
    /// This function requires Lean runtime promise support which may not be
    /// available in all Lean versions. The `lean_promise_new` function is not
    /// currently exported from the Lean shared library.
    #[allow(unreachable_code)]
    pub fn new(_lean: Lean<'l>) -> Self {
        // TODO: lean_promise_new is not exported from libleanshared.so
        // This needs to be implemented when/if Lean exports these functions
        unimplemented!(
            "Promise creation requires lean_promise_new which is not exported from Lean shared library"
        );
    }

    // ========================================================================
    // Resolution
    // ========================================================================

    /// Resolve this promise with a value.
    ///
    /// This completes the associated task with the given value.
    ///
    /// # Important
    ///
    /// - This consumes the promise (it can only be resolved once)
    /// - The value is consumed and transferred to the waiting task
    ///
    /// # Note
    ///
    /// This function requires Lean runtime promise support which may not be
    /// available in all Lean versions.
    #[allow(unreachable_code)]
    pub fn resolve(self, _value: LeanBound<'l, T>) {
        // TODO: lean_promise_resolve is not exported from libleanshared.so
        unimplemented!(
            "Promise resolution requires lean_promise_resolve which is not exported from Lean shared library"
        );
    }

    // ========================================================================
    // Task Access
    // ========================================================================

    /// Get the task associated with this promise.
    ///
    /// The returned task will complete when this promise is resolved.
    /// Multiple calls return independent references to the same underlying task.
    ///
    /// # Note
    ///
    /// This function requires Lean runtime promise support which may not be
    /// available in all Lean versions.
    #[allow(unreachable_code)]
    pub fn task(&self) -> LeanTask<'l, T> {
        // TODO: lean_promise_get_task is not exported from libleanshared.so
        unimplemented!(
            "Promise task access requires lean_promise_get_task which is not exported from Lean shared library"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_promise_type_size() {
        // LeanPromise should be pointer-sized (same as LeanBound)
        assert_eq!(
            std::mem::size_of::<LeanPromise<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
