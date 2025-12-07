//! Lean string type wrapper.

use crate::ffi;
use crate::marker::Lean;
use crate::instance::LeanBound;
use crate::err::{LeanResult, LeanError};
use std::ffi::CStr;

/// A Lean string object.
pub struct LeanString {
    _private: (),
}

impl LeanString {
    /// Create a new Lean string from a Rust string.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s = LeanString::new(lean, "Hello, Lean!")?;
    /// ```
    pub fn new<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanBound<'l, Self>> {
        let c_str = std::ffi::CString::new(s)
            .map_err(|_| LeanError::conversion("String contains null byte"))?;

        unsafe {
            let ptr = ffi::lean_mk_string(c_str.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the string as a Rust `&str`.
    pub fn to_str<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<&'l str> {
        unsafe {
            let c_str = ffi::lean_string_cstr(obj.as_ptr());
            let cstr = CStr::from_ptr(c_str);
            cstr.to_str()
                .map_err(|e| LeanError::conversion(&format!("Invalid UTF-8: {}", e)))
        }
    }

    /// Get the length of the string in bytes.
    pub fn len<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::lean_string_len(obj.as_ptr()) }
    }

    /// Check if the string is empty.
    pub fn is_empty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::len(obj) == 0
    }
}
