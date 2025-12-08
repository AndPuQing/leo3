//! Smart pointers for managing Lean objects.
//!
//! This module provides safe wrappers around Lean object pointers with
//! automatic reference counting.

use crate::ffi;
use crate::marker::Lean;
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
        ffi::object::lean_inc_ref(ptr);
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
            ffi::object::lean_inc_ref(self.inner.as_ptr());
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
            ffi::object::lean_inc_ref(self.inner.as_ptr());
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
            ffi::object::lean_inc_ref(self.inner.as_ptr());
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
}
