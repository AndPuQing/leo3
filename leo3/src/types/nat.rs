//! Lean natural number type wrapper.

use crate::ffi;
use crate::marker::Lean;
use crate::instance::LeanBound;
use crate::err::{LeanResult, LeanError};

/// A Lean natural number object.
pub struct LeanNat {
    _private: (),
}

impl LeanNat {
    /// Create a Lean natural number from a Rust usize.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 42)?;
    /// ```
    pub fn from_usize<'l>(lean: Lean<'l>, n: usize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_usize_to_nat(n);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert a Lean natural number to a Rust usize.
    ///
    /// Returns an error if the number doesn't fit in usize.
    pub fn to_usize<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<usize> {
        unsafe {
            if ffi::lean_nat_is_small(obj.as_ptr()) {
                Ok(ffi::lean_nat_to_usize(obj.as_ptr()))
            } else {
                Err(LeanError::conversion("Natural number too large for usize"))
            }
        }
    }

    /// Check if this natural number fits in a usize.
    pub fn is_small<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::lean_nat_is_small(obj.as_ptr()) }
    }
}
