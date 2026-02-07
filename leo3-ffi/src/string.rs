//! FFI bindings for Lean4 string operations
//!
//! Based on the string functions from lean.h

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};
use libc::{c_char, size_t};

extern "C" {
    /// Get UTF-8 string length in characters
    ///
    /// # Safety
    /// - `str` must be a valid null-terminated UTF-8 string
    pub fn lean_utf8_strlen(str: *const c_char) -> size_t;

    /// Get UTF-8 string length in characters (bounded by n bytes)
    ///
    /// # Safety
    /// - `str` must be a valid UTF-8 string of at least `n` bytes
    pub fn lean_utf8_n_strlen(str: *const c_char, n: size_t) -> size_t;

    /// Create a new Lean string from C string (unchecked)
    ///
    /// # Safety
    /// - `s` must be a valid UTF-8 string
    /// - `sz` is the byte size
    /// - `len` is the character length
    pub fn lean_mk_string_unchecked(s: *const c_char, sz: size_t, len: size_t) -> lean_obj_res;

    /// Create a new Lean string from bytes
    ///
    /// # Safety
    /// - `s` must be a valid UTF-8 byte sequence
    /// - `sz` is the byte size
    pub fn lean_mk_string_from_bytes(s: *const c_char, sz: size_t) -> lean_obj_res;

    /// Create a new Lean string from bytes (unchecked)
    ///
    /// # Safety
    /// - `s` must be a valid UTF-8 byte sequence
    /// - `sz` is the byte size (no validation performed)
    pub fn lean_mk_string_from_bytes_unchecked(s: *const c_char, sz: size_t) -> lean_obj_res;

    /// Create a new Lean string from ASCII C string (unchecked)
    ///
    /// # Safety
    /// - `s` must be a valid null-terminated ASCII string
    pub fn lean_mk_ascii_string_unchecked(s: *const c_char) -> lean_obj_res;

    /// Create a new Lean string from C string
    ///
    /// # Safety
    /// - `s` must be a valid null-terminated UTF-8 string
    pub fn lean_mk_string(s: *const c_char) -> lean_obj_res;

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

    /// Get UTF-8 character at position (cold path)
    ///
    /// # Safety
    /// - `str` must be a valid UTF-8 string
    /// - `i` must be < size
    /// - `c` is the byte at position i
    pub fn lean_string_utf8_get_fast_cold(
        str: *const c_char,
        i: size_t,
        size: size_t,
        c: u8,
    ) -> u32;

    /// Get next UTF-8 byte position
    ///
    /// # Safety
    /// - `s` must be a valid string object
    /// - `i` must be a valid byte position (boxed usize)
    pub fn lean_string_utf8_next(s: b_lean_obj_arg, i: b_lean_obj_arg) -> lean_obj_res;

    /// Get next UTF-8 byte position (cold path)
    ///
    /// # Safety
    /// - `i` is the current position
    /// - `c` is the byte at position i
    pub fn lean_string_utf8_next_fast_cold(i: size_t, c: u8) -> lean_obj_res;

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
    pub fn lean_string_utf8_extract(
        s: b_lean_obj_arg,
        b: b_lean_obj_arg,
        e: b_lean_obj_arg,
    ) -> lean_obj_res;

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

    /// Compute hash of a string
    ///
    /// # Safety
    /// - `s` must be a valid string object
    pub fn lean_string_hash(s: b_lean_obj_arg) -> u64;

    /// Convert usize to string
    ///
    /// # Safety
    /// - Always safe to call
    pub fn lean_string_of_usize(n: size_t) -> lean_obj_res;

    /// Compare string regions using memcmp
    ///
    /// # Safety
    /// - `s1` and `s2` must be valid string objects
    /// - `lstart`, `rstart`, and `len` must be valid byte positions (boxed usize)
    ///   Returns: 0 if equal, 1 if s1 > s2, 2 if s1 < s2
    pub fn lean_string_memcmp(
        s1: b_lean_obj_arg,
        s2: b_lean_obj_arg,
        lstart: b_lean_obj_arg,
        rstart: b_lean_obj_arg,
        len: b_lean_obj_arg,
    ) -> u8;
}

// ============================================================================
// String Slice Operations (Lean 4.26.0+)
// ============================================================================

#[cfg(lean_4_26)]
extern "C" {
    /// Compute hash of a string slice
    ///
    /// # Safety
    /// - `s` must be a valid string slice object
    ///
    /// Note: This function is only available in Lean 4.26.0+
    pub fn lean_slice_hash(s: b_lean_obj_arg) -> u64;

    /// Compare two string slices lexicographically (decidable less-than)
    ///
    /// # Safety
    /// - `s1` and `s2` must be valid string slice objects
    ///   Returns: 1 if s1 < s2, 0 otherwise
    ///
    /// Note: This function is only available in Lean 4.26.0+
    pub fn lean_slice_dec_lt(s1: b_lean_obj_arg, s2: b_lean_obj_arg) -> u8;

    /// Compare string slice regions using memcmp
    ///
    /// # Safety
    /// - `s1` and `s2` must be valid string slice objects
    /// - `lstart`, `rstart`, and `len` must be valid byte positions (boxed usize)
    ///   Returns: 0 if equal, 1 if s1 > s2, 2 if s1 < s2
    ///
    /// Note: This function is only available in Lean 4.26.0+
    pub fn lean_slice_memcmp(
        s1: b_lean_obj_arg,
        s2: b_lean_obj_arg,
        lstart: b_lean_obj_arg,
        rstart: b_lean_obj_arg,
        len: b_lean_obj_arg,
    ) -> u8;
}

// Inline helper functions from lean.h

/// Get string length as boxed object
#[inline]
pub unsafe fn lean_string_length(s: b_lean_obj_arg) -> lean_obj_res {
    crate::object::lean_box(crate::inline::lean_string_len(s))
}

/// Get string byte size as boxed object (size - 1, excluding null terminator)
#[inline]
pub unsafe fn lean_string_utf8_byte_size(s: b_lean_obj_arg) -> lean_obj_res {
    crate::object::lean_box(crate::inline::lean_string_size(s) - 1)
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
    crate::object::lean_unbox(i) >= crate::inline::lean_string_size(s) - 1
}

/// Get byte at position (fast path, no bounds check)
#[inline]
pub unsafe fn lean_string_get_byte_fast(s: b_lean_obj_arg, i: b_lean_obj_arg) -> u8 {
    let cstr = crate::inline::lean_string_cstr(s);
    let idx = crate::object::lean_unbox(i);
    *cstr.add(idx) as u8
}
