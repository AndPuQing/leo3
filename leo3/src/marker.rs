//! The `Lean<'l>` token for compile-time Lean runtime verification.
//!
//! This module defines the core `Lean<'l>` type, which serves as proof that
//! the Lean runtime is initialized. All Lean operations require a `Lean<'l>`
//! token, ensuring memory safety at compile time.

use std::marker::PhantomData;

/// A token that proves the Lean runtime is initialized.
///
/// This type is used throughout Leo3 to ensure that Lean objects are only
/// accessed when the runtime is properly initialized. The `'l` lifetime
/// parameter ties all Lean objects to the initialization scope.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
///
/// fn process_data<'l>(lean: Lean<'l>) -> LeanResult<()> {
///     // Create Lean objects using the token
///     let s = LeanString::mk(lean, "Hello");
///     Ok(())
/// }
/// ```
///
/// # Safety
///
/// The `Lean<'l>` token is typically created by `with_lean()` or similar
/// functions that ensure proper initialization. Users should not create
/// this token manually except in very specific circumstances.
#[derive(Copy, Clone)]
pub struct Lean<'l> {
    // PhantomData to bind the 'l lifetime
    _marker: PhantomData<&'l ()>,
    // Ensure !Send and !Sync (Lean is not thread-safe by default)
    _not_send: PhantomData<*mut ()>,
}

impl<'l> Lean<'l> {
    /// Create a new `Lean<'l>` token.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the Lean runtime is properly initialized
    /// before calling this function. This is typically done by calling
    /// `prepare_freethreaded_lean()`.
    ///
    /// This function should generally not be called directly by users.
    /// Use `with_lean()` instead.
    #[inline]
    pub unsafe fn assume_initialized() -> Self {
        Lean {
            _marker: PhantomData,
            _not_send: PhantomData,
        }
    }

    /// Get a pointer to the Lean runtime context.
    ///
    /// This is used internally for FFI calls that require context.
    /// Most users won't need to call this directly.
    #[inline]
    pub fn as_ptr(self) -> *mut std::ffi::c_void {
        // Lean4 doesn't have a direct context pointer like Python's GIL
        // This is a placeholder for future runtime context support
        std::ptr::null_mut()
    }
}

// Note: Lean<'l> is automatically !Send and !Sync due to PhantomData<*mut ()>
// The *mut () in _not_send ensures the type is not Send or Sync

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_token_size() {
        // Lean token should be zero-sized
        assert_eq!(std::mem::size_of::<Lean>(), 0);
    }
}
