//! FFI bindings for Lean4 string operations
//!
//! Based on the string functions from lean.h

use libc::{c_char, size_t};
use crate::object::{lean_obj_arg, lean_obj_res, b_lean_obj_arg};

extern "C" {
    /// Create a new Lean string from C string
    ///
    /// # Safety
    /// - `s` must be a valid null-terminated UTF-8 string
    pub fn lean_mk_string(s: *const c_char) -> lean_obj_res;

    /// Get C string pointer from Lean string
    ///
    /// # Safety
    /// - `o` must be a valid string object
    /// - Returned pointer is valid only while object is alive
    pub fn lean_string_cstr(o: b_lean_obj_arg) -> *const c_char;

    /// Get string size in bytes (including null terminator)
    ///
    /// # Safety
    /// - `o` must be a valid string object
    pub fn lean_string_size(o: b_lean_obj_arg) -> size_t;

    /// Get string length in UTF-8 characters
    ///
    /// # Safety
    /// - `o` must be a valid string object
    pub fn lean_string_len(o: b_lean_obj_arg) -> size_t;

    /// Push a UTF-32 character to the end of a string
    ///
    /// # Safety
    /// - `s` must be a valid string object (consumed)
    /// - Returns a new string with the character appended
    pub fn lean_string_push(s: lean_obj_arg, c: u32) -> lean_obj_res;

    /// Append two strings
    ///
    /// # Safety
    /// - `s1` must be a valid string object (consumed)
    /// - `s2` must be a valid string object (borrowed)
    pub fn lean_string_append(s1: lean_obj_arg, s2: b_lean_obj_arg) -> lean_obj_res;

    /// Create a string from a list of characters
    ///
    /// # Safety
    /// - `cs` must be a valid list object (consumed)
    pub fn lean_string_mk(cs: lean_obj_arg) -> lean_obj_res;

    /// Convert string to list of characters
    ///
    /// # Safety
    /// - `s` must be a valid string object (consumed)
    pub fn lean_string_data(s: lean_obj_arg) -> lean_obj_res;

    /// Get UTF-8 character at byte position
    ///
    /// # Safety
    /// - `s` must be a valid string object
    /// - `i` must be a valid byte position (boxed usize)
    pub fn lean_string_utf8_get(s: b_lean_obj_arg, i: b_lean_obj_arg) -> u32;

    /// Get next UTF-8 byte position
    ///
    /// # Safety
    /// - `s` must be a valid string object
    /// - `i` must be a valid byte position (boxed usize)
    pub fn lean_string_utf8_next(s: b_lean_obj_arg, i: b_lean_obj_arg) -> lean_obj_res;

    /// Get previous UTF-8 byte position
    ///
    /// # Safety
    /// - `s` must be a valid string object
    /// - `i` must be a valid byte position (boxed usize)
    pub fn lean_string_utf8_prev(s: b_lean_obj_arg, i: b_lean_obj_arg) -> lean_obj_res;

    /// Set UTF-8 character at position
    ///
    /// # Safety
    /// - `s` must be a valid string object (consumed)
    /// - `i` must be a valid byte position (boxed usize)
    /// - `c` is the UTF-32 character to set
    pub fn lean_string_utf8_set(s: lean_obj_arg, i: b_lean_obj_arg, c: u32) -> lean_obj_res;

    /// Extract substring
    ///
    /// # Safety
    /// - `s` must be a valid string object
    /// - `b` and `e` must be valid byte positions (boxed usize)
    pub fn lean_string_utf8_extract(s: b_lean_obj_arg, b: b_lean_obj_arg, e: b_lean_obj_arg) -> lean_obj_res;

    /// Compare two strings for equality (cold path)
    ///
    /// # Safety
    /// - `s1` and `s2` must be valid string objects
    pub fn lean_string_eq_cold(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> bool;

    /// Compare two strings lexicographically
    ///
    /// # Safety
    /// - `s1` and `s2` must be valid string objects
    pub fn lean_string_lt(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> bool;
}

// Inline helper functions from lean.h

/// Get string length as boxed object
#[inline]
pub unsafe fn lean_string_length(s: b_lean_obj_arg) -> lean_obj_res {
    crate::object::lean_box(lean_string_len(s))
}

/// Get string byte size as boxed object (size - 1, excluding null terminator)
#[inline]
pub unsafe fn lean_string_utf8_byte_size(s: b_lean_obj_arg) -> lean_obj_res {
    crate::object::lean_box(lean_string_size(s) - 1)
}

/// Compare two strings for equality (fast path checks pointer equality first)
#[inline]
pub unsafe fn lean_string_eq(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> bool {
    s1 == s2 || lean_string_eq_cold(s1, s2)
}

/// Compare two strings for inequality
#[inline]
pub unsafe fn lean_string_ne(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> bool {
    !lean_string_eq(s1, s2)
}

/// Check if iterator is at end of string
#[inline]
pub unsafe fn lean_string_utf8_at_end(s: b_lean_obj_arg, i: b_lean_obj_arg) -> bool {
    crate::object::lean_unbox(i) >= lean_string_size(s) - 1
}

/// Get byte at position (fast path, no bounds check)
#[inline]
pub unsafe fn lean_string_get_byte_fast(s: b_lean_obj_arg, i: b_lean_obj_arg) -> u8 {
    let cstr = lean_string_cstr(s);
    let idx = crate::object::lean_unbox(i);
    *cstr.add(idx) as u8
}
