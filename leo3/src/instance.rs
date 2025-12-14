//! Smart pointers for managing Lean objects.
//!
//! This module provides safe wrappers around Lean object pointers with
//! automatic reference counting.
//!
//! # Type Hierarchy
//!
//! ```text
//! LeanBound<'l, T>  ──unbind()──────>  LeanRef<T>
//!       │                                  │
//!       │                                  │
//!       └──unbind_mt()──> LeanUnbound<T> <─┴─into_unbound()
//! ```
//!
//! - **`LeanBound<'l, T>`**: Lifetime-bound, `!Send + !Sync` (tied to runtime)
//! - **`LeanRef<T>`**: Unbound but NOT guaranteed MT-safe
//! - **`LeanUnbound<T>`**: Thread-safe, automatically marked for MT use

use crate::ffi;
use crate::marker::Lean;
use crate::unbound::LeanUnbound;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A Lean object bound to a `Lean<'l>` lifetime.
///
/// This is the primary type for working with Lean objects. It automatically
/// manages reference counting and ensures the object is only accessed while
/// the Lean runtime is initialized.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// fn example<'l>(lean: Lean<'l>) -> LeanResult<()> {
///     let obj = LeanBound::from_owned_ptr(lean, some_lean_ptr);
///     // obj will automatically dec_ref when dropped
///     Ok(())
/// }
/// ```
#[repr(transparent)]
pub struct LeanBound<'l, T = LeanAny> {
    inner: NonNull<ffi::lean_object>,
    _marker: PhantomData<&'l T>,
}

impl<'l, T> LeanBound<'l, T> {
    /// Create a `LeanBound` from an owned pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must be a valid Lean object pointer
    /// - The caller transfers ownership to this `LeanBound`
    /// - The reference count must already be incremented for this instance
    #[inline]
    pub unsafe fn from_owned_ptr(_lean: Lean<'l>, ptr: *mut ffi::lean_object) -> Self {
        Self {
            inner: NonNull::new_unchecked(ptr),
            _marker: PhantomData,
        }
    }

    /// Create a `LeanBound` from a borrowed pointer.
    ///
    /// This will increment the reference count.
    ///
    /// # Safety
    ///
    /// - `ptr` must be a valid Lean object pointer
    #[inline]
    pub unsafe fn from_borrowed_ptr(_lean: Lean<'l>, ptr: *const ffi::lean_object) -> Self {
        let ptr = ptr as *mut ffi::lean_object;
        ffi::object::lean_inc(ptr);
        Self {
            inner: NonNull::new_unchecked(ptr),
            _marker: PhantomData,
        }
    }

    /// Get the raw pointer to the Lean object.
    ///
    /// The pointer is valid as long as this `LeanBound` is alive.
    #[inline]
    pub fn as_ptr(&self) -> *mut ffi::lean_object {
        self.inner.as_ptr()
    }

    /// Consume this `LeanBound` and return the raw pointer.
    ///
    /// The caller is responsible for managing the reference count.
    #[inline]
    pub fn into_ptr(self) -> *mut ffi::lean_object {
        let ptr = self.inner.as_ptr();
        std::mem::forget(self); // Don't dec_ref
        ptr
    }

    /// Unbind this object from the `Lean<'l>` lifetime.
    ///
    /// This converts `LeanBound<'l, T>` to `LeanRef<T>`, which can be
    /// stored and used across initialization boundaries.
    #[inline]
    pub fn unbind(self) -> LeanRef<T> {
        let ptr = self.into_ptr();
        unsafe { LeanRef::from_owned_ptr(ptr) }
    }

    /// Get a `Lean<'l>` token from this bound object.
    ///
    /// This is safe because `LeanBound<'l, T>` can only exist if
    /// a `Lean<'l>` token was used to create it, proving the runtime
    /// is initialized for the 'l lifetime.
    #[inline]
    pub fn lean_token(&self) -> Lean<'l> {
        unsafe { Lean::assume_initialized() }
    }

    /// Cast this `LeanBound<'l, T>` to `LeanBound<'l, U>`.
    ///
    /// This is safe because all Lean objects share the same underlying
    /// representation. The type parameter is only used for type safety
    /// at the Rust level.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n: LeanBound<LeanNat> = LeanNat::from_usize(lean, 42)?;
    /// let any: LeanBound<LeanAny> = n.cast();
    /// ```
    #[inline]
    pub fn cast<U>(self) -> LeanBound<'l, U> {
        let lean = self.lean_token();
        let ptr = self.into_ptr();
        unsafe { LeanBound::from_owned_ptr(lean, ptr) }
    }

    /// Unbind this object for thread-safe use.
    ///
    /// This converts `LeanBound<'l, T>` to `LeanUnbound<T>`, which is `Send + Sync`.
    /// The object is automatically marked for multi-threaded use via `lean_mark_mt()`,
    /// enabling atomic reference counting.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use std::thread;
    ///
    /// let s = LeanString::mk(lean, "Hello").unwrap();
    /// let unbound = s.unbind_mt();
    ///
    /// // Can now be sent to another thread
    /// thread::spawn(move || {
    ///     with_lean(|lean| {
    ///         let bound = unbound.bind(lean);
    ///         // use bound...
    ///     });
    /// });
    /// ```
    ///
    /// # Performance Note
    ///
    /// This method marks the object (and all reachable objects) for multi-threaded
    /// use, which switches to atomic reference counting. For single-threaded code,
    /// prefer `unbind()` which doesn't incur this overhead.
    #[inline]
    pub fn unbind_mt(self) -> LeanUnbound<T> {
        let ptr = self.into_ptr();
        // SAFETY: We just consumed a valid LeanBound, the pointer is valid
        unsafe { LeanUnbound::from_owned_ptr(ptr) }
    }
}

impl<'l, T> Drop for LeanBound<'l, T> {
    fn drop(&mut self) {
        unsafe {
            ffi::object::lean_dec(self.inner.as_ptr() as *mut _);
        }
    }
}

impl<'l, T> Clone for LeanBound<'l, T> {
    fn clone(&self) -> Self {
        unsafe {
            ffi::object::lean_inc(self.inner.as_ptr());
        }
        Self {
            inner: self.inner,
            _marker: PhantomData,
        }
    }
}

/// An owned reference to a Lean object.
///
/// Unlike `LeanBound`, this is not tied to a `Lean<'l>` lifetime, so it can
/// be stored in structs and sent across threads (if the underlying type is Send).
///
/// To use a `LeanRef`, convert it to a `LeanBound` using `bind()`.
pub struct LeanRef<T = LeanAny> {
    inner: NonNull<ffi::lean_object>,
    _marker: PhantomData<T>,
}

impl<T> LeanRef<T> {
    /// Bind this reference to a `Lean<'l>` lifetime.
    ///
    /// This converts `LeanRef<T>` to `LeanBound<'l, T>` for use with Lean APIs.
    #[inline]
    pub fn bind<'l>(&self, _lean: Lean<'l>) -> LeanBound<'l, T> {
        unsafe {
            ffi::object::lean_inc(self.inner.as_ptr());
        }
        LeanBound {
            inner: self.inner,
            _marker: PhantomData,
        }
    }

    /// Create a `LeanRef` from an owned pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must be a valid Lean object pointer
    /// - The reference count must already be incremented for this instance
    #[inline]
    pub unsafe fn from_owned_ptr(ptr: *mut ffi::lean_object) -> Self {
        Self {
            inner: NonNull::new_unchecked(ptr),
            _marker: PhantomData,
        }
    }

    /// Get the raw pointer to the Lean object.
    #[inline]
    pub fn as_ptr(&self) -> *mut ffi::lean_object {
        self.inner.as_ptr()
    }

    /// Convert this `LeanRef` to a thread-safe `LeanUnbound`.
    ///
    /// This marks the object for multi-threaded use via `lean_mark_mt()`,
    /// enabling atomic reference counting.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let lean_ref: LeanRef<LeanString> = bound.unbind();
    /// let unbound: LeanUnbound<LeanString> = lean_ref.into_unbound();
    /// // unbound can now be safely sent across threads
    /// ```
    #[inline]
    pub fn into_unbound(self) -> LeanUnbound<T> {
        LeanUnbound::from_ref(self)
    }
}

impl<T> Drop for LeanRef<T> {
    fn drop(&mut self) {
        unsafe {
            ffi::object::lean_dec(self.inner.as_ptr());
        }
    }
}

impl<T> Clone for LeanRef<T> {
    fn clone(&self) -> Self {
        unsafe {
            ffi::object::lean_inc(self.inner.as_ptr());
        }
        Self {
            inner: self.inner,
            _marker: PhantomData,
        }
    }
}

unsafe impl<T: Send> Send for LeanRef<T> {}
unsafe impl<T: Sync> Sync for LeanRef<T> {}

/// Marker type for any Lean object.
///
/// This is the base type for all Lean objects.
pub struct LeanAny {
    _private: (),
}

/// A borrowed reference to a Lean object with no reference counting overhead.
///
/// This provides zero-cost access to Lean objects when you don't need ownership.
/// Unlike [`LeanBound`], this type does not increment or decrement the reference
/// count, making it more efficient for temporary access patterns.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the borrow (how long this reference is valid)
/// - `'l`: The Lean runtime lifetime (proves the runtime is initialized)
///
/// # Safety
///
/// Because `LeanBorrowed` does not manage reference counts, the underlying
/// object must be kept alive by another reference (like a [`LeanBound`])
/// for the duration of the borrow. This is enforced by the `'a` lifetime.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// fn example<'l>(lean: Lean<'l>, bound: &LeanBound<'l, LeanString>) {
///     let borrowed = bound.as_borrowed();
///     // Use borrowed for efficient read access
///     // borrowed is automatically valid for the same lifetime as the borrow of bound
/// }
/// ```
#[repr(transparent)]
pub struct LeanBorrowed<'a, 'l, T = LeanAny> {
    inner: *const ffi::lean_object,
    _borrow: PhantomData<&'a ()>,
    _lean: PhantomData<&'l T>,
}

// LeanBorrowed is Copy because it doesn't manage any resources
impl<'a, 'l, T> Copy for LeanBorrowed<'a, 'l, T> {}

impl<'a, 'l, T> Clone for LeanBorrowed<'a, 'l, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'l, T> LeanBorrowed<'a, 'l, T> {
    /// Create a `LeanBorrowed` from a raw pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must be a valid Lean object pointer
    /// - The caller must ensure the object remains valid for lifetime `'a`
    /// - The Lean runtime must be initialized for lifetime `'l`
    #[inline]
    pub unsafe fn from_ptr(ptr: *const ffi::lean_object) -> Self {
        Self {
            inner: ptr,
            _borrow: PhantomData,
            _lean: PhantomData,
        }
    }

    /// Get the raw pointer to the Lean object.
    ///
    /// The pointer is valid as long as the underlying object is alive.
    #[inline]
    pub fn as_ptr(&self) -> *const ffi::lean_object {
        self.inner
    }

    /// Get a mutable pointer to the Lean object.
    ///
    /// # Safety
    ///
    /// The caller must ensure exclusive access to the object.
    #[inline]
    pub fn as_mut_ptr(&self) -> *mut ffi::lean_object {
        self.inner as *mut ffi::lean_object
    }

    /// Get a `Lean<'l>` token from this borrowed reference.
    ///
    /// This is safe because `LeanBorrowed<'a, 'l, T>` can only exist if
    /// the Lean runtime is initialized for the `'l` lifetime.
    #[inline]
    pub fn lean_token(&self) -> Lean<'l> {
        unsafe { Lean::assume_initialized() }
    }

    /// Upgrade this borrowed reference to an owned [`LeanBound`].
    ///
    /// This increments the reference count and returns an owned reference
    /// that will decrement the count when dropped.
    #[inline]
    pub fn to_owned(&self) -> LeanBound<'l, T> {
        unsafe {
            ffi::object::lean_inc(self.inner as *mut _);
            LeanBound::from_owned_ptr(self.lean_token(), self.inner as *mut _)
        }
    }

    /// Cast this `LeanBorrowed<'a, 'l, T>` to `LeanBorrowed<'a, 'l, U>`.
    ///
    /// This is safe because all Lean objects share the same underlying
    /// representation. The type parameter is only used for type safety
    /// at the Rust level.
    #[inline]
    pub fn cast<U>(self) -> LeanBorrowed<'a, 'l, U> {
        LeanBorrowed {
            inner: self.inner,
            _borrow: PhantomData,
            _lean: PhantomData,
        }
    }
}

impl<'l, T> LeanBound<'l, T> {
    /// Borrow this `LeanBound` as a `LeanBorrowed`.
    ///
    /// This provides zero-cost access without affecting the reference count.
    /// The returned `LeanBorrowed` is valid for the lifetime of the borrow.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let bound: LeanBound<LeanString> = ...;
    /// let borrowed = bound.as_borrowed();
    /// // Use borrowed for efficient read access
    /// ```
    #[inline]
    pub fn as_borrowed(&self) -> LeanBorrowed<'_, 'l, T> {
        LeanBorrowed {
            inner: self.inner.as_ptr() as *const _,
            _borrow: PhantomData,
            _lean: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leanbound_size() {
        // LeanBound should be pointer-sized
        assert_eq!(
            std::mem::size_of::<LeanBound<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_leanref_size() {
        // LeanRef should be pointer-sized
        assert_eq!(
            std::mem::size_of::<LeanRef<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_leanborrowed_size() {
        // LeanBorrowed should be pointer-sized (same as LeanBound)
        assert_eq!(
            std::mem::size_of::<LeanBorrowed<LeanAny>>(),
            std::mem::size_of::<*mut ()>()
        );
    }

    #[test]
    fn test_leanborrowed_is_copy() {
        // Verify LeanBorrowed implements Copy by using it in a context that requires Copy
        fn assert_copy<T: Copy>() {}
        assert_copy::<LeanBorrowed<LeanAny>>();
    }
}
