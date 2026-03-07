//! Core object, reference-counting, and constructor inline helpers.

use super::{
    layout::{
        lean_array_object, lean_closure_object, lean_ctor_object, lean_external_object,
        lean_promise_object, lean_ref_object, lean_sarray_object, lean_string_object,
        lean_task_object, lean_thunk_object,
    },
    likely,
};
use crate::{
    object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res, lean_object},
    LEAN_ARRAY, LEAN_CLOSURE, LEAN_EXTERNAL, LEAN_MAX_CTOR_TAG, LEAN_MPZ, LEAN_PROMISE, LEAN_REF,
    LEAN_SCALAR_ARRAY, LEAN_STRING, LEAN_TASK, LEAN_THUNK,
};
use libc::{c_uint, size_t};
use std::sync::atomic::{AtomicI32, Ordering};

// Core Object Functions
// ============================================================================

#[inline(always)]
pub unsafe fn lean_is_scalar(o: *const lean_object) -> bool {
    ((o as size_t) & 1) == 1
}

#[inline(always)]
pub unsafe fn lean_box(n: size_t) -> lean_obj_res {
    ((n << 1) | 1) as lean_obj_res
}

#[inline(always)]
pub unsafe fn lean_unbox(o: b_lean_obj_arg) -> size_t {
    (o as size_t) >> 1
}

#[inline(always)]
pub unsafe fn lean_ptr_tag(o: *const lean_object) -> u8 {
    (*o).m_tag
}

#[inline(always)]
pub unsafe fn lean_ptr_other(o: *const lean_object) -> u8 {
    (*o).m_other
}

// ============================================================================
// Reference Counting
// ============================================================================

#[inline(always)]
#[allow(dead_code)]
unsafe fn lean_is_mt(o: *mut lean_object) -> bool {
    (*o).m_rc < 0
}

#[inline(always)]
unsafe fn lean_is_st(o: *mut lean_object) -> bool {
    (*o).m_rc > 0
}

#[inline]
pub unsafe fn lean_has_rc(o: *const lean_object) -> bool {
    (*o).m_rc != 0
}

#[inline]
pub unsafe fn lean_is_shared(o: *const lean_object) -> bool {
    if likely(lean_is_st(o as *mut lean_object)) {
        (*o).m_rc > 1
    } else {
        false
    }
}

#[inline(always)]
unsafe fn lean_get_rc_mt_addr(o: *mut lean_object) -> *mut AtomicI32 {
    &mut (*o).m_rc as *mut _ as *mut AtomicI32
}

#[inline]
pub unsafe fn lean_inc_ref_n(o: *mut lean_object, n: size_t) {
    if likely(lean_is_st(o)) {
        (*o).m_rc = (*o).m_rc.wrapping_add(n as i32);
    } else if (*o).m_rc != 0 {
        // Only increment for non-persistent objects (m_rc != 0)
        // This includes both multi-threaded (m_rc < 0) objects
        (*lean_get_rc_mt_addr(o)).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

#[inline(always)]
pub unsafe fn lean_inc_ref(o: *mut lean_object) {
    lean_inc_ref_n(o, 1);
}

/// Increment reference count (with scalar check).
///
/// # Safety
/// - `o` can be any lean object (scalar or pointer)
#[inline(always)]
pub unsafe fn lean_inc(o: lean_obj_arg) {
    if !lean_is_scalar(o) {
        lean_inc_ref(o);
    }
}

/// Increment reference count by n (with scalar check).
///
/// # Safety
/// - `o` can be any lean object (scalar or pointer)
#[inline(always)]
pub unsafe fn lean_inc_n(o: lean_obj_arg, n: size_t) {
    if !lean_is_scalar(o) {
        lean_inc_ref_n(o, n);
    }
}

extern "C" {
    fn lean_dec_ref_cold(o: *mut lean_object);
}

#[inline(always)]
pub unsafe fn lean_dec_ref(o: *mut lean_object) {
    if likely((*o).m_rc > 1) {
        (*o).m_rc -= 1;
    } else if (*o).m_rc != 0 {
        lean_dec_ref_cold(o);
    }
}

/// Decrement reference count (with scalar check).
///
/// # Safety
/// - `o` can be any lean object (scalar or pointer)
#[inline(always)]
pub unsafe fn lean_dec(o: lean_obj_arg) {
    if !lean_is_scalar(o) {
        lean_dec_ref(o);
    }
}

/// Check if an object is exclusively owned (refcount == 1).
///
/// # Safety
/// - `o` must be a valid non-scalar object pointer
#[inline]
pub unsafe fn lean_is_exclusive(o: *mut lean_object) -> bool {
    if likely(lean_is_st(o)) {
        (*o).m_rc == 1
    } else {
        false
    }
}

// ============================================================================
// Object tag tests and casts
// ============================================================================

#[inline(always)]
pub unsafe fn lean_is_ctor(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) <= LEAN_MAX_CTOR_TAG
}

#[inline(always)]
pub unsafe fn lean_is_closure(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_CLOSURE
}

#[inline(always)]
pub unsafe fn lean_is_array(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_ARRAY
}

#[inline(always)]
pub unsafe fn lean_is_sarray(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_SCALAR_ARRAY
}

#[inline(always)]
pub unsafe fn lean_is_string(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_STRING
}

#[inline(always)]
pub unsafe fn lean_is_mpz(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_MPZ
}

#[inline(always)]
pub unsafe fn lean_is_thunk(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_THUNK
}

#[inline(always)]
pub unsafe fn lean_is_task(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_TASK
}

#[inline(always)]
pub unsafe fn lean_is_promise(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_PROMISE
}

#[inline(always)]
pub unsafe fn lean_is_external(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_EXTERNAL
}

#[inline(always)]
pub unsafe fn lean_is_ref(o: lean_obj_arg) -> bool {
    lean_ptr_tag(o) == LEAN_REF
}

#[inline]
pub unsafe fn lean_obj_tag(o: lean_obj_arg) -> u8 {
    if lean_is_scalar(o) {
        lean_unbox(o) as u8
    } else {
        lean_ptr_tag(o)
    }
}

#[inline(always)]
pub unsafe fn lean_to_ctor(o: lean_obj_arg) -> *mut lean_ctor_object {
    debug_assert!(lean_is_ctor(o));
    o as *mut lean_ctor_object
}

#[inline(always)]
pub unsafe fn lean_to_closure(o: lean_obj_arg) -> *mut lean_closure_object {
    debug_assert!(lean_is_closure(o));
    o as *mut lean_closure_object
}

#[inline(always)]
pub unsafe fn lean_to_array(o: lean_obj_arg) -> *mut lean_array_object {
    debug_assert!(lean_is_array(o));
    o as *mut lean_array_object
}

#[inline(always)]
pub unsafe fn lean_to_sarray(o: lean_obj_arg) -> *mut lean_sarray_object {
    debug_assert!(lean_is_sarray(o));
    o as *mut lean_sarray_object
}

#[inline(always)]
pub unsafe fn lean_to_string(o: lean_obj_arg) -> *mut lean_string_object {
    debug_assert!(lean_is_string(o));
    o as *mut lean_string_object
}

#[inline(always)]
pub unsafe fn lean_to_thunk(o: lean_obj_arg) -> *mut lean_thunk_object {
    debug_assert!(lean_is_thunk(o));
    o as *mut lean_thunk_object
}

#[inline(always)]
pub unsafe fn lean_to_task(o: lean_obj_arg) -> *mut lean_task_object {
    debug_assert!(lean_is_task(o));
    o as *mut lean_task_object
}

#[inline(always)]
pub unsafe fn lean_to_promise(o: lean_obj_arg) -> *mut lean_promise_object {
    debug_assert!(lean_is_promise(o));
    o as *mut lean_promise_object
}

#[inline(always)]
pub unsafe fn lean_to_ref(o: lean_obj_arg) -> *mut lean_ref_object {
    debug_assert!(lean_is_ref(o));
    o as *mut lean_ref_object
}

#[inline(always)]
pub unsafe fn lean_to_external(o: lean_obj_arg) -> *mut lean_external_object {
    debug_assert!(lean_is_external(o));
    o as *mut lean_external_object
}

// ============================================================================
// Constructor Object Accessors
// ============================================================================

/// Get the number of object fields in a constructor.
#[inline(always)]
pub unsafe fn lean_ctor_num_objs(o: *const lean_object) -> u8 {
    debug_assert!(lean_is_ctor(o as *mut lean_object));
    lean_ptr_other(o)
}

/// Get a pointer to the object array in a constructor.
#[inline(always)]
pub unsafe fn lean_ctor_obj_cptr(o: *mut lean_object) -> *mut *mut lean_object {
    debug_assert!(lean_is_ctor(o));
    // SAFETY: constructor objects store their object fields immediately after
    // the header; `m_objs` is the zero-length array anchor for that region.
    (*lean_to_ctor(o)).m_objs.as_mut_ptr()
}

#[inline(always)]
unsafe fn lean_ctor_offset_cptr(o: *mut lean_object, offset: c_uint) -> *mut u8 {
    debug_assert!(
        offset as usize >= lean_ctor_num_objs(o) as usize * std::mem::size_of::<*mut lean_object>()
    );
    (lean_ctor_obj_cptr(o) as *mut u8).add(offset as usize)
}

/// Get a pointer to the scalar data in a constructor.
///
/// Scalars are stored after the object pointers.
#[inline(always)]
pub unsafe fn lean_ctor_scalar_cptr(o: *mut lean_object) -> *mut u8 {
    debug_assert!(lean_is_ctor(o));
    lean_ctor_obj_cptr(o).add(lean_ctor_num_objs(o) as usize) as *mut u8
}

/// Get a constructor field.
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `i` must be < lean_ctor_num_objs(o)
#[inline(always)]
pub unsafe fn lean_ctor_get(o: b_lean_obj_arg, i: u32) -> *const lean_object {
    debug_assert!((i as u8) < lean_ctor_num_objs(o));
    *lean_ctor_obj_cptr(o as *mut lean_object).add(i as usize) as *const lean_object
}

/// Set a constructor field.
///
/// # Safety
/// - `o` must be a valid, exclusive constructor object
/// - `i` must be < lean_ctor_num_objs(o)
/// - Consumes ownership of `v`
#[inline(always)]
pub unsafe fn lean_ctor_set(o: lean_obj_arg, i: u32, v: lean_obj_arg) {
    debug_assert!((i as u8) < lean_ctor_num_objs(o));
    *lean_ctor_obj_cptr(o).add(i as usize) = v;
}

#[inline(always)]
pub unsafe fn lean_ctor_set_tag(o: lean_obj_arg, new_tag: u8) {
    debug_assert!(new_tag <= LEAN_MAX_CTOR_TAG);
    (*o).m_tag = new_tag;
}

#[inline(always)]
pub unsafe fn lean_ctor_release(o: lean_obj_arg, i: c_uint) {
    debug_assert!((i as u8) < lean_ctor_num_objs(o));
    let objs = lean_ctor_obj_cptr(o);
    let obj = *objs.add(i as usize);
    lean_dec(obj);
    *objs.add(i as usize) = lean_box(0);
}

// ============================================================================

/// Get uint8 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid within scalar area
#[inline]
pub unsafe fn lean_ctor_get_uint8(o: b_lean_obj_arg, offset: c_uint) -> u8 {
    *lean_ctor_offset_cptr(o as *mut lean_object, offset)
}

/// Set uint8 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid within scalar area
#[inline]
pub unsafe fn lean_ctor_set_uint8(o: lean_obj_arg, offset: c_uint, v: u8) {
    *lean_ctor_offset_cptr(o, offset) = v;
}

/// Get uint16 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 2-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint16(o: b_lean_obj_arg, offset: c_uint) -> u16 {
    *(lean_ctor_offset_cptr(o as *mut lean_object, offset) as *const u16)
}

/// Set uint16 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 2-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint16(o: lean_obj_arg, offset: c_uint, v: u16) {
    *(lean_ctor_offset_cptr(o, offset) as *mut u16) = v;
}

/// Get uint32 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 4-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint32(o: b_lean_obj_arg, offset: c_uint) -> u32 {
    *(lean_ctor_offset_cptr(o as *mut lean_object, offset) as *const u32)
}

/// Set uint32 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 4-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint32(o: lean_obj_arg, offset: c_uint, v: u32) {
    *(lean_ctor_offset_cptr(o, offset) as *mut u32) = v;
}

/// Get uint64 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 8-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint64(o: b_lean_obj_arg, offset: c_uint) -> u64 {
    *(lean_ctor_offset_cptr(o as *mut lean_object, offset) as *const u64)
}

/// Set uint64 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 8-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint64(o: lean_obj_arg, offset: c_uint, v: u64) {
    *(lean_ctor_offset_cptr(o, offset) as *mut u64) = v;
}

#[inline]
pub unsafe fn lean_ctor_get_float(o: b_lean_obj_arg, offset: c_uint) -> f64 {
    *(lean_ctor_offset_cptr(o as *mut lean_object, offset) as *const f64)
}

#[inline]
pub unsafe fn lean_ctor_set_float(o: lean_obj_arg, offset: c_uint, v: f64) {
    *(lean_ctor_offset_cptr(o, offset) as *mut f64) = v;
}

#[inline]
pub unsafe fn lean_ctor_get_float32(o: b_lean_obj_arg, offset: c_uint) -> f32 {
    *(lean_ctor_offset_cptr(o as *mut lean_object, offset) as *const f32)
}

#[inline]
pub unsafe fn lean_ctor_set_float32(o: lean_obj_arg, offset: c_uint, v: f32) {
    *(lean_ctor_offset_cptr(o, offset) as *mut f32) = v;
}

/// Get usize scalar from constructor
///
/// Note: The index `i` is into the object array, not a byte offset.
/// The function accesses scalar storage after the object pointers.
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `i` must be >= lean_ctor_num_objs(o)
#[inline]
pub unsafe fn lean_ctor_get_usize(o: b_lean_obj_arg, i: c_uint) -> size_t {
    debug_assert!(i as u8 >= lean_ctor_num_objs(o));
    *(lean_ctor_obj_cptr(o as *mut lean_object).add(i as usize) as *const size_t)
}

/// Set usize scalar in constructor
///
/// Note: The index `i` is into the object array, not a byte offset.
/// The function accesses scalar storage after the object pointers.
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `i` must be >= lean_ctor_num_objs(o)
#[inline]
pub unsafe fn lean_ctor_set_usize(o: lean_obj_arg, i: c_uint, v: size_t) {
    debug_assert!(i as u8 >= lean_ctor_num_objs(o));
    *(lean_ctor_obj_cptr(o).add(i as usize) as *mut size_t) = v;
}

/// Set the header of a lean object
///
/// # Safety
/// - `o` must point to a valid lean_object with allocated space
/// - This initializes the reference count to 1
#[inline]
pub unsafe fn lean_set_st_header(o: *mut lean_object, tag: u8, other: u8) {
    (*o).m_rc = 1;
    (*o).m_tag = tag;
    (*o).m_other = other;
    // Note: m_cs_sz is already initialized by lean_alloc_object when using mimalloc
    // For non-mimalloc builds, we set it to 0 here
    (*o).m_cs_sz = 0;
}

// ============================================================================

/// Allocate a small object (inline helper)
///
/// This is a simplified version that uses lean_alloc_object
#[inline(always)]
pub unsafe fn lean_alloc_small_object(sz: c_uint) -> *mut lean_object {
    use crate::object::lean_alloc_object;
    lean_alloc_object(sz as size_t)
}
