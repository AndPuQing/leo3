//! Lean except/result type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;

/// A Lean except (result) object.
///
/// Except in Lean4 is inductively defined:
/// ```lean
/// inductive Except (ε : Type u) (α : Type v) where
///   | error : ε → Except ε α
///   | ok    : α → Except ε α
/// ```
///
/// This is Lean's equivalent to Rust's `Result<T, E>` type, but with
/// the error type (ε) listed first.
pub struct LeanExcept {
    _private: (),
}

impl LeanExcept {
    /// Create an Except with an error value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Except.error` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let err_msg = LeanString::mk(lean, "something went wrong")?;
    ///     let result = LeanExcept::error(lean, err_msg.cast())?;
    ///     assert!(LeanExcept::isError(&result));
    ///     Ok(())
    /// })
    /// ```
    pub fn error<'l>(
        lean: Lean<'l>,
        error: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Except.error is constructor 0 with 1 field (the error value)
            let ptr = ffi::lean_alloc_ctor(0, 1, 0);
            ffi::lean_ctor_set(ptr, 0, error.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an Except with a success value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Except.ok` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let value = LeanNat::from_usize(lean, 42)?;
    /// let result = LeanExcept::ok(lean, value.cast())?;
    /// assert!(LeanExcept::isOk(&result));
    /// ```
    pub fn ok<'l>(
        lean: Lean<'l>,
        value: LeanBound<'l, LeanAny>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Except.ok is constructor 1 with 1 field (the success value)
            let ptr = ffi::lean_alloc_ctor(1, 1, 0);
            ffi::lean_ctor_set(ptr, 0, value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if the except is an error.
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `Except.error` in Lean4.
    #[allow(non_snake_case)]
    pub fn isError<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let tag = ffi::lean_obj_tag(obj.as_ptr());
            tag == 0 // error has tag 0
        }
    }

    /// Check if the except is ok (success).
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `Except.ok` in Lean4.
    #[allow(non_snake_case)]
    pub fn isOk<'l>(obj: &LeanBound<'l, Self>) -> bool {
        !Self::isError(obj)
    }

    /// Get the error value if this is an error.
    ///
    /// Returns `None` if this is an ok value.
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `error e` in Lean4.
    pub fn get_error<'l>(
        lean: Lean<'l>,
        obj: &LeanBound<'l, Self>,
    ) -> Option<LeanBound<'l, LeanAny>> {
        if !Self::isError(obj) {
            return None;
        }

        unsafe {
            let err_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(err_ptr);
            Some(LeanBound::from_owned_ptr(lean, err_ptr))
        }
    }

    /// Get the success value if this is ok.
    ///
    /// Returns `None` if this is an error value.
    ///
    /// # Lean4 Reference
    /// Similar to pattern matching on `ok val` in Lean4.
    pub fn get_ok<'l>(lean: Lean<'l>, obj: &LeanBound<'l, Self>) -> Option<LeanBound<'l, LeanAny>> {
        if Self::isError(obj) {
            return None;
        }

        unsafe {
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            // Increment ref count since we're borrowing
            ffi::lean_inc(val_ptr);
            Some(LeanBound::from_owned_ptr(lean, val_ptr))
        }
    }

    /// Convert to Rust Result.
    ///
    /// Returns `Ok(value)` if this is an ok value, or `Err(error)` if this is an error.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let result = LeanExcept::ok(lean, value)?;
    /// match LeanExcept::toRustResult(lean, &result) {
    ///     Ok(val) => println!("Success: {:?}", val),
    ///     Err(err) => println!("Error: {:?}", err),
    /// }
    /// ```
    #[allow(non_snake_case)]
    pub fn toRustResult<'l>(
        lean: Lean<'l>,
        obj: &LeanBound<'l, Self>,
    ) -> Result<LeanBound<'l, LeanAny>, LeanBound<'l, LeanAny>> {
        if Self::isError(obj) {
            Err(Self::get_error(lean, obj).expect("error value must exist"))
        } else {
            Ok(Self::get_ok(lean, obj).expect("ok value must exist"))
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanExcept> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if LeanExcept::isError(self) {
            write!(f, "LeanExcept::error(...)")
        } else {
            write!(f, "LeanExcept::ok(...)")
        }
    }
}
