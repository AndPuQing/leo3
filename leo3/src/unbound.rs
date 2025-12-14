//! Thread-safe smart pointer for Lean objects.
//!
//! This module provides `LeanUnbound<T>`, a smart pointer type that can be safely
//! sent and shared across threads. Unlike `LeanBound<'l, T>`, it is not tied to
//! a `Lean<'l>` lifetime, making it suitable for storage in long-lived structures
//! and cross-thread communication.
//!
//! # Thread Safety Model
//!
//! Lean4 uses a dual-mode reference counting system:
//! - **ST (Single-Threaded)**: `m_rc > 0` - Non-atomic reference counting (faster)
//! - **MT (Multi-Threaded)**: `m_rc < 0` - Atomic reference counting (thread-safe)
//! - **Persistent**: `m_rc == 0` - Never freed, always safe
//!
//! When an object is marked for multi-threaded use via `lean_mark_mt()`, it and
//! all transitively reachable objects are switched to atomic reference counting.
//! This is a one-way transition - once marked MT, an object stays MT.
//!
//! `LeanUnbound<T>` automatically calls `lean_mark_mt()` on creation, ensuring
//! all contained objects are safe for cross-thread access.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use std::thread;
//!
//! fn example<'l>(lean: Lean<'l>) {
//!     // Create a Lean string and unbind it for thread-safe use
//!     let s = LeanString::mk(lean, "Hello, World!").unwrap();
//!     let unbound: LeanUnbound<LeanString> = s.unbind_mt();
//!
//!     // Now we can send it to another thread
//!     let handle = thread::spawn(move || {
//!         // Use with_lean or similar to get a Lean token
//!         with_lean(|lean| {
//!             let bound = unbound.bind(lean);
//!             // Use bound...
//!         });
//!     });
//!     handle.join().unwrap();
//! }
//! ```

use crate::ffi;
use crate::instance::{LeanAny, LeanBound, LeanRef};
use crate::marker::Lean;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A thread-safe owned reference to a Lean object.
///
/// This type is the thread-safe equivalent of `LeanRef<T>`. Unlike `LeanRef`,
/// `LeanUnbound` guarantees that the underlying object has been marked for
/// multi-threaded use (`lean_mark_mt`), making atomic reference counting active.
///
/// # When to Use
///
/// Use `LeanUnbound<T>` when you need to:
/// - Store Lean objects in `Arc<Mutex<...>>` or other concurrent data structures
/// - Send Lean objects between threads
/// - Store Lean objects in long-lived data structures that may outlive any single `Lean<'l>` scope
///
/// # Performance Note
///
/// Because `LeanUnbound` uses atomic reference counting (after `lean_mark_mt`),
/// it has slightly higher overhead than `LeanBound` or `LeanRef` for single-threaded
/// use. Prefer `LeanBound` for code that doesn't need thread safety.
///
/// # Relationship to Other Types
///
/// ```text
/// LeanBound<'l, T>  ──unbind_mt()──>  LeanUnbound<T>
///       │                                  │
///       │                                  │
///       └──unbind()──> LeanRef<T> ─into_unbound()─┘
///                          │
///                     (Send+Sync but
///                      NOT guaranteed MT)
/// ```
#[repr(transparent)]
pub struct LeanUnbound<T = LeanAny> {
    inner: NonNull<ffi::lean_object>,
    _marker: PhantomData<T>,
}

// SAFETY: LeanUnbound guarantees the object has been marked MT via lean_mark_mt(),
// which enables atomic reference counting. This makes it safe to send across threads.
unsafe impl<T: Send> Send for LeanUnbound<T> {}

// SAFETY: LeanUnbound uses atomic reference counting (after lean_mark_mt),
// so multiple threads can safely hold references to the same object.
unsafe impl<T: Sync> Sync for LeanUnbound<T> {}

impl<T> LeanUnbound<T> {
    /// Create a new `LeanUnbound` from an owned pointer, marking it for MT use.
    ///
    /// This is the primary constructor. It calls `lean_mark_mt()` to ensure
    /// the object (and all transitively reachable objects) use atomic reference
    /// counting.
    ///
    /// # Safety
    ///
    /// - `ptr` must be a valid Lean object pointer
    /// - The caller transfers ownership to this `LeanUnbound`
    /// - The reference count must already be incremented for this instance
    #[inline]
    pub unsafe fn from_owned_ptr(ptr: *mut ffi::lean_object) -> Self {
        debug_assert!(
            !ptr.is_null(),
            "LeanUnbound::from_owned_ptr called with null pointer"
        );

        // Mark the object for multi-threaded use (atomic reference counting)
        // This is safe because we own the reference and are about to make it thread-safe
        if !ffi::inline::lean_is_scalar(ptr) {
            ffi::object::lean_mark_mt(ptr);
        }

        Self {
            inner: NonNull::new_unchecked(ptr),
            _marker: PhantomData,
        }
    }

    /// Create a `LeanUnbound` from a `LeanRef`, marking it for MT use.
    ///
    /// This consumes the `LeanRef` and ensures the object is marked for
    /// multi-threaded use.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let lean_ref: LeanRef<LeanString> = bound.unbind();
    /// let unbound: LeanUnbound<LeanString> = LeanUnbound::from_ref(lean_ref);
    /// ```
    #[inline]
    pub fn from_ref(lean_ref: LeanRef<T>) -> Self {
        // Prevent drop from running - we're taking ownership
        let ptr = lean_ref.as_ptr();
        std::mem::forget(lean_ref);

        // SAFETY: LeanRef guarantees the pointer is valid and owned
        unsafe { Self::from_owned_ptr(ptr) }
    }

    /// Bind this unbound reference to a `Lean<'l>` lifetime.
    ///
    /// This creates a new `LeanBound` that shares ownership with this `LeanUnbound`.
    /// The reference count is incremented, so both references remain valid.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let bound: LeanBound<'l, T> = unbound.bind(lean);
    /// // Both unbound and bound are valid and can be used
    /// ```
    #[inline]
    pub fn bind<'l>(&self, lean: Lean<'l>) -> LeanBound<'l, T> {
        unsafe {
            ffi::object::lean_inc(self.inner.as_ptr());
            LeanBound::from_owned_ptr(lean, self.inner.as_ptr())
        }
    }

    /// Consume this `LeanUnbound` and bind it to a `Lean<'l>` lifetime.
    ///
    /// This converts the `LeanUnbound` to a `LeanBound` without changing
    /// the reference count.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let bound: LeanBound<'l, T> = unbound.into_bound(lean);
    /// // unbound is consumed, only bound remains
    /// ```
    #[inline]
    pub fn into_bound<'l>(self, lean: Lean<'l>) -> LeanBound<'l, T> {
        let ptr = self.into_ptr();
        unsafe { LeanBound::from_owned_ptr(lean, ptr) }
    }

    /// Get the raw pointer to the Lean object.
    ///
    /// The pointer is valid as long as this `LeanUnbound` is alive.
    #[inline]
    pub fn as_ptr(&self) -> *mut ffi::lean_object {
        self.inner.as_ptr()
    }

    /// Consume this `LeanUnbound` and return the raw pointer.
    ///
    /// The caller is responsible for managing the reference count.
    #[inline]
    pub fn into_ptr(self) -> *mut ffi::lean_object {
        let ptr = self.inner.as_ptr();
        std::mem::forget(self);
        ptr
    }

    /// Create a clone with an incremented reference count.
    ///
    /// This is the explicit cloning method, similar to PyO3's `clone_ref()`.
    /// Since we're in MT mode, this uses atomic increment.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let clone = original.clone_ref();
    /// // Both original and clone are valid
    /// ```
    #[inline]
    pub fn clone_ref(&self) -> Self {
        unsafe {
            ffi::object::lean_inc(self.inner.as_ptr());
            Self {
                inner: self.inner,
                _marker: PhantomData,
            }
        }
    }

    /// Check if this and another `LeanUnbound` point to the same object.
    ///
    /// This is a pointer equality check, not a value equality check.
    #[inline]
    pub fn is<U>(&self, other: &LeanUnbound<U>) -> bool {
        std::ptr::eq(self.as_ptr(), other.as_ptr())
    }

    /// Cast this `LeanUnbound<T>` to `LeanUnbound<U>`.
    ///
    /// This is safe because all Lean objects share the same underlying
    /// representation. The type parameter is only used for type safety
    /// at the Rust level.
    #[inline]
    pub fn cast<U>(self) -> LeanUnbound<U> {
        let ptr = self.into_ptr();
        unsafe {
            LeanUnbound {
                inner: NonNull::new_unchecked(ptr),
                _marker: PhantomData,
            }
        }
    }

    /// Cast this `LeanUnbound<T>` to `LeanUnbound<LeanAny>`.
    ///
    /// Convenience method for upcasting to the any type.
    #[inline]
    pub fn into_any(self) -> LeanUnbound<LeanAny> {
        self.cast()
    }

    /// Get a reference as `&LeanUnbound<LeanAny>`.
    #[inline]
    pub fn as_any(&self) -> &LeanUnbound<LeanAny> {
        // SAFETY: LeanUnbound has the same layout regardless of T
        unsafe { &*(self as *const Self as *const LeanUnbound<LeanAny>) }
    }

    /// Check if the underlying object is a scalar (immediate value).
    ///
    /// Scalars are small integers that are encoded directly in the pointer,
    /// not heap-allocated. They don't need reference counting.
    #[inline]
    pub fn is_scalar(&self) -> bool {
        unsafe { ffi::inline::lean_is_scalar(self.inner.as_ptr()) }
    }

    /// Convert to a `LeanRef<T>`.
    ///
    /// Note: The resulting `LeanRef` will already be in MT mode since this
    /// `LeanUnbound` was created with `lean_mark_mt()`.
    #[inline]
    pub fn into_ref(self) -> LeanRef<T> {
        let ptr = self.into_ptr();
        unsafe { LeanRef::from_owned_ptr(ptr) }
    }
}

impl<T> Drop for LeanUnbound<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            // lean_dec handles both scalars and MT objects correctly
            ffi::object::lean_dec(self.inner.as_ptr());
        }
    }
}

impl<T> Clone for LeanUnbound<T> {
    #[inline]
    fn clone(&self) -> Self {
        self.clone_ref()
    }
}

impl<T> std::fmt::Debug for LeanUnbound<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LeanUnbound")
            .field("ptr", &self.inner.as_ptr())
            .finish()
    }
}

impl<T> From<LeanRef<T>> for LeanUnbound<T> {
    #[inline]
    fn from(lean_ref: LeanRef<T>) -> Self {
        Self::from_ref(lean_ref)
    }
}

// Conversion from LeanBound requires going through unbind_mt
// This is intentionally NOT implemented as From to make the MT marking explicit

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leanunbound_size() {
        // LeanUnbound should be pointer-sized
        assert_eq!(
            std::mem::size_of::<LeanUnbound<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_leanunbound_is_send_sync() {
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}

        // These will fail to compile if LeanUnbound is not Send+Sync
        assert_send::<LeanUnbound<LeanAny>>();
        assert_sync::<LeanUnbound<LeanAny>>();
    }
}
