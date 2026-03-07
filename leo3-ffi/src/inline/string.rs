//! String-related inline helpers.

use super::{layout::lean_string_object, object::lean_to_string};
use crate::object::{b_lean_obj_arg, lean_obj_arg};
use libc::size_t;

/// Get C string pointer from Lean string
#[inline]
pub unsafe fn lean_string_cstr(o: b_lean_obj_arg) -> *const libc::c_char {
    // SAFETY: Lean strings store UTF-8 bytes inline after the header, and
    // `lean_to_string` verifies the runtime tag before exposing that payload.
    (*lean_to_string(o as lean_obj_arg)).m_data.as_ptr() as *const libc::c_char
}

/// Get string length (number of UTF-8 characters)
#[inline]
pub unsafe fn lean_string_len(o: b_lean_obj_arg) -> size_t {
    // SAFETY: `lean_string_object` matches Lean's header-plus-trailing-bytes
    // layout, so reading the cached character length field is layout-correct.
    let str_obj = o as *const lean_string_object;
    (*str_obj).m_length
}

/// Get string size in bytes (including null terminator)
#[inline]
pub unsafe fn lean_string_size(o: b_lean_obj_arg) -> size_t {
    // SAFETY: the string header stores the total byte size alongside the UTF-8
    // payload, so this cast only reads the fixed-size header prefix.
    let str_obj = o as *const lean_string_object;
    (*str_obj).m_size
}

// ============================================================================
