//! IO operations for Lean4.
//!
//! This module provides safe wrappers around Lean4's IO primitives,
//! including file operations, environment variables, and console I/O.
//!
//! # Example
//!
//! ```rust,ignore
//! use leo3::prelude::*;
//! use leo3::io::fs;
//!
//! fn main() -> LeanResult<()> {
//!     leo3::prepare_freethreaded_lean();
//!
//!     leo3::with_lean(|lean| {
//!         // Read a file
//!         let content = fs::read_file(lean, "config.txt")?;
//!         println!("Content: {}", content);
//!
//!         // Write a file
//!         fs::write_file(lean, "output.txt", "Hello, Lean!")?;
//!
//!         Ok(())
//!     })
//! }
//! ```

use crate::conversion::FromLean;
use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use std::marker::PhantomData;

pub mod env;
pub mod error;
pub mod fs;

pub use error::{IOError, IOResult};

/// A Lean IO computation that produces a value of type `T`.
///
/// This corresponds to Lean4's `IO T` type. It represents a computation
/// that performs IO and produces a value of type `T`, or fails with an `IO.Error`.
///
/// # Example
///
/// ```rust,ignore
/// use leo3::prelude::*;
/// use leo3::io::LeanIO;
///
/// fn example<'l>(lean: Lean<'l>) -> LeanResult<()> {
///     // Create an IO computation
///     let io_computation: LeanIO<String> = /* ... */;
///
///     // Execute it
///     let result: String = io_computation.run()?;
///
///     Ok(())
/// }
/// ```
#[repr(transparent)]
pub struct LeanIO<'l, T> {
    /// The underlying Lean IO object (IO T)
    inner: LeanBound<'l, LeanIOAny>,
    _phantom: PhantomData<T>,
}

impl<'l, T: 'l> LeanIO<'l, T> {
    /// Create a `LeanIO` from a Lean object.
    ///
    /// # Safety
    ///
    /// - `obj` must be a valid Lean IO object of type `IO T`
    #[inline]
    pub unsafe fn from_raw(obj: LeanBound<'l, LeanIOAny>) -> Self {
        LeanIO {
            inner: obj,
            _phantom: PhantomData,
        }
    }

    /// Execute the IO computation and return the result.
    ///
    /// This corresponds to Lean's `unsafe_perform_io` or running IO in the main function.
    ///
    /// # Errors
    ///
    /// Returns an error if the IO computation fails.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let io: LeanIO<String> = /* ... */;
    /// let result: String = io.run()?;
    /// ```
    pub fn run(self) -> LeanResult<T>
    where
        T: FromLean<'l>,
    {
        let lean = self.inner.lean_token();

        // Execute IO with a RealWorld token
        unsafe {
            let world = ffi::io::lean_io_mk_world();
            let io_fn = self.inner.into_ptr();

            // Apply the IO function to the world token
            // IO functions have type: RealWorld → Except IO.Error (T × RealWorld)
            let result = ffi::closure::lean_apply_1(io_fn, world);

            // Check if result is an error
            if io_result_is_error(result) {
                // Extract error
                let err_ptr = io_result_get_error(result);
                let error = IOError::from_lean_io_error(lean, err_ptr);
                return Err(error.into());
            }

            // Extract the successful value
            // The result is (T × RealWorld), we need the first component
            let ok_ptr = io_result_get_value(result);
            let bound: LeanBound<LeanAny> = LeanBound::from_owned_ptr(lean, ok_ptr);

            // The value is a pair (T, RealWorld)
            // Constructor tag 0 (Prod.mk) with 2 fields
            let value_ptr = ffi::object::lean_ctor_get(bound.as_ptr(), 0);
            let value_bound: LeanBound<LeanAny> = LeanBound::from_borrowed_ptr(lean, value_ptr);

            // Convert to Rust type
            let typed: LeanBound<T::Source> = value_bound.cast();
            T::from_lean(&typed)
        }
    }

    /// Get the underlying Lean object.
    ///
    /// This consumes the `LeanIO` and returns the raw Lean object.
    #[inline]
    pub fn into_inner(self) -> LeanBound<'l, LeanIOAny> {
        self.inner
    }

    /// Get a reference to the underlying Lean object.
    #[inline]
    pub fn as_inner(&self) -> &LeanBound<'l, LeanIOAny> {
        &self.inner
    }
}

/// Marker type for IO computations.
///
/// This is used as the type parameter for `LeanBound` when wrapping IO objects.
pub struct LeanIOAny {
    _private: (),
}

// ============================================================================
// IO.Result helpers
// ============================================================================

/// Lean4 `IO.Result` is represented as `Except IO.Error (T × RealWorld)`.
/// `Except.ok` has tag 0 and one field (value), `Except.error` has tag 1 and one field (error).
#[inline]
unsafe fn io_result_is_error(res: *mut ffi::lean_object) -> bool {
    ffi::object::lean_obj_tag(res) != 0
}

#[inline]
unsafe fn io_result_get_error(res: *mut ffi::lean_object) -> *mut ffi::lean_object {
    ffi::object::lean_ctor_get(res, 0) as *mut ffi::lean_object
}

#[inline]
unsafe fn io_result_get_value(res: *mut ffi::lean_object) -> *mut ffi::lean_object {
    ffi::object::lean_ctor_get(res, 0) as *mut ffi::lean_object
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_io_type_size() {
        // LeanIO should be pointer-sized
        assert_eq!(
            std::mem::size_of::<LeanIO<String>>(),
            std::mem::size_of::<*mut ()>()
        );
    }
}
