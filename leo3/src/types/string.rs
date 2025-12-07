//! Lean string type wrapper.

use crate::err::{LeanError, LeanResult};
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use std::ffi::CStr;

/// A Lean string object.
///
/// Provides safe wrappers around Lean's UTF-8 string type.
pub struct LeanString {
    _private: (),
}

impl LeanString {
    /// Create a new Lean string from a Rust string.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let s = LeanString::new(lean, "Hello, Lean!")?;
    ///     println!("{}", LeanString::to_str(&s)?);
    ///     Ok(())
    /// })
    /// ```
    pub fn new<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanBound<'l, Self>> {
        let c_str = std::ffi::CString::new(s)
            .map_err(|_| LeanError::conversion("String contains null byte"))?;

        unsafe {
            let ptr = ffi::string::lean_mk_string(c_str.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the string as a Rust `&str`.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s = LeanString::new(lean, "Hello")?;
    /// assert_eq!(LeanString::to_str(&s)?, "Hello");
    /// ```
    pub fn to_str<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<&'l str> {
        unsafe {
            let c_str = ffi::string::leo3_string_cstr(obj.as_ptr());
            let cstr = CStr::from_ptr(c_str);
            cstr.to_str()
                .map_err(|e| LeanError::conversion(&format!("Invalid UTF-8: {}", e)))
        }
    }

    /// Get the UTF-8 length of the string (number of characters).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s = LeanString::new(lean, "Hello")?;
    /// assert_eq!(LeanString::len(&s), 5);
    /// ```
    pub fn len<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::string::leo3_string_len(obj.as_ptr()) }
    }

    /// Get the byte size of the string.
    pub fn byte_size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::string::lean_string_size(obj.as_ptr()) }
    }

    /// Check if the string is empty.
    pub fn is_empty<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::len(obj) == 0
    }

    /// Append a UTF-32 character to the string.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s = LeanString::new(lean, "Hello")?;
    /// let s = LeanString::push(s, '!' as u32)?;
    /// assert_eq!(LeanString::to_str(&s)?, "Hello!");
    /// ```
    pub fn push<'l>(s: LeanBound<'l, Self>, c: u32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = s.lean_token();
            let ptr = ffi::string::lean_string_push(s.into_ptr(), c);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Append another string to this string.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s1 = LeanString::new(lean, "Hello, ")?;
    /// let s2 = LeanString::new(lean, "World!")?;
    /// let result = LeanString::append(s1, &s2)?;
    /// assert_eq!(LeanString::to_str(&result)?, "Hello, World!");
    /// ```
    pub fn append<'l>(
        s1: LeanBound<'l, Self>,
        s2: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = s1.lean_token();
            let ptr = ffi::string::lean_string_append(s1.into_ptr(), s2.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Compare two strings for equality.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s1 = LeanString::new(lean, "hello")?;
    /// let s2 = LeanString::new(lean, "hello")?;
    /// assert!(LeanString::eq(&s1, &s2));
    /// ```
    pub fn eq<'l>(s1: &LeanBound<'l, Self>, s2: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::string::lean_string_eq(s1.as_ptr(), s2.as_ptr()) }
    }

    /// Compare two strings lexicographically.
    ///
    /// Returns true if s1 < s2.
    pub fn lt<'l>(s1: &LeanBound<'l, Self>, s2: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::string::lean_string_lt(s1.as_ptr(), s2.as_ptr()) }
    }

    /// Extract a substring from byte positions.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let s = LeanString::new(lean, "Hello, World!")?;
    /// let sub = LeanString::substring(lean, &s, 0, 5)?;
    /// assert_eq!(LeanString::to_str(&sub)?, "Hello");
    /// ```
    pub fn substring<'l>(
        lean: Lean<'l>,
        s: &LeanBound<'l, Self>,
        start: usize,
        end: usize,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let start_boxed = ffi::lean_box(start);
            let end_boxed = ffi::lean_box(end);
            let ptr = ffi::string::lean_string_utf8_extract(s.as_ptr(), start_boxed, end_boxed);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get a UTF-32 character at a byte position.
    ///
    /// # Safety
    /// - `pos` must be a valid UTF-8 boundary
    pub fn get_char<'l>(s: &LeanBound<'l, Self>, pos: usize) -> u32 {
        unsafe {
            let pos_boxed = ffi::lean_box(pos);
            ffi::string::lean_string_utf8_get(s.as_ptr(), pos_boxed)
        }
    }

    /// Get the next UTF-8 byte position.
    ///
    /// # Safety
    /// - `pos` must be a valid UTF-8 boundary
    pub fn next_pos<'l>(s: &LeanBound<'l, Self>, pos: usize) -> usize {
        unsafe {
            let pos_boxed = ffi::lean_box(pos);
            let result = ffi::string::lean_string_utf8_next(s.as_ptr(), pos_boxed);
            ffi::lean_unbox(result)
        }
    }

    /// Get the previous UTF-8 byte position.
    ///
    /// # Safety
    /// - `pos` must be a valid UTF-8 boundary
    pub fn prev_pos<'l>(s: &LeanBound<'l, Self>, pos: usize) -> usize {
        unsafe {
            let pos_boxed = ffi::lean_box(pos);
            let result = ffi::string::lean_string_utf8_prev(s.as_ptr(), pos_boxed);
            ffi::lean_unbox(result)
        }
    }
}

// Implement Display for convenient printing (requires to_str conversion)
impl<'l> std::fmt::Debug for LeanBound<'l, LeanString> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match LeanString::to_str(self) {
            Ok(s) => write!(f, "LeanString({:?})", s),
            Err(_) => write!(f, "LeanString(<invalid UTF-8>)"),
        }
    }
}
