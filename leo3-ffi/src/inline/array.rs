//! Scalar-array and byte-array inline helpers.

use super::{
    layout::lean_sarray_object,
    object::{lean_is_scalar, lean_set_st_header, lean_to_sarray, lean_unbox},
};
use crate::{
    object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res},
    LEAN_SCALAR_ARRAY,
};
use libc::{c_uint, size_t};

extern "C" {
    fn lean_internal_panic_out_of_memory() -> !;
}

/// Allocate a scalar array with given element size, size, and capacity
///
/// # Safety
/// - elem_size must be valid (typically 1, 4, or 8)
/// - capacity must be reasonable to avoid OOM
#[inline]
pub unsafe fn lean_alloc_sarray(elem_size: c_uint, size: size_t, capacity: size_t) -> lean_obj_res {
    let total_size = std::mem::size_of::<lean_sarray_object>() + (elem_size as usize) * capacity;
    let o_raw = crate::object::lean_alloc_object(total_size);

    lean_set_st_header(o_raw, LEAN_SCALAR_ARRAY, elem_size as u8);

    // SAFETY: after writing the scalar-array header, the allocation matches the
    // layout of `lean_sarray_object`, so the cast mirrors Lean's inline helper.
    let o = lean_to_sarray(o_raw);

    // Initialize size and capacity
    (*o).m_size = size;
    (*o).m_capacity = capacity;

    o as lean_obj_res
}

/// Create an empty byte array with capacity
///
/// # Safety
/// - `capacity` must be a boxed usize
#[inline]
pub unsafe fn lean_mk_empty_byte_array(capacity: b_lean_obj_arg) -> lean_obj_res {
    if !lean_is_scalar(capacity as lean_obj_arg) {
        lean_internal_panic_out_of_memory();
    }
    lean_alloc_sarray(1, 0, lean_unbox(capacity))
}

/// Get the size of a scalar array.
///
/// # Safety
/// - `o` must be a valid scalar array object
#[inline]
pub unsafe fn lean_sarray_size(o: b_lean_obj_arg) -> size_t {
    let sarray = o as *const lean_sarray_object;
    (*sarray).m_size
}

/// Get the capacity of a scalar array.
///
/// # Safety
/// - `o` must be a valid scalar array object
#[inline]
pub unsafe fn lean_sarray_capacity(o: lean_obj_arg) -> size_t {
    let sarray = o as *const lean_sarray_object;
    (*sarray).m_capacity
}

/// Get a pointer to the data of a scalar array.
///
/// # Safety
/// - `o` must be a valid scalar array object
#[inline]
pub unsafe fn lean_sarray_cptr(o: lean_obj_arg) -> *mut u8 {
    let sarray = lean_to_sarray(o);
    // SAFETY: `m_data` is the zero-length trailing storage region for the array
    // payload, so taking its mutable pointer is the supported C layout trick.
    (*sarray).m_data.as_mut_ptr()
}

/// Get a byte from a byte array (unchecked).
///
/// # Safety
/// - `a` must be a valid byte array
/// - `i` must be < lean_sarray_size(a)
#[inline]
pub unsafe fn lean_byte_array_uget(a: b_lean_obj_arg, i: size_t) -> u8 {
    debug_assert!(i < lean_sarray_size(a));
    *lean_sarray_cptr(a as lean_obj_arg).add(i)
}

/// Set a byte in a byte array (unchecked).
///
/// # Safety
/// - `a` must be a valid, exclusive byte array
/// - `i` must be < lean_sarray_size(a)
#[inline]
pub unsafe fn lean_byte_array_uset(a: lean_obj_arg, i: size_t, v: u8) -> lean_obj_arg {
    *lean_sarray_cptr(a).add(i) = v;
    a
}
