//! Rust re-implementations of Lean4's static inline functions
//!
//! Lean4's C API defines many functions as `static inline` in lean.h,
//! which means they don't exist as linkable symbols. Following PyO3's
//! approach, we manually re-implement these in Rust with #[inline] attributes.
//!
//! These implementations are based on Lean4 v4.25.2 headers.

use crate::{
    object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res, lean_object},
    LEAN_ARRAY, LEAN_CLOSURE, LEAN_EXTERNAL, LEAN_MAX_CTOR_TAG, LEAN_MPZ, LEAN_PROMISE, LEAN_REF,
    LEAN_SCALAR_ARRAY, LEAN_STRING, LEAN_TASK, LEAN_THUNK,
};
use libc::{c_void, size_t};
use std::sync::atomic::{AtomicI32, AtomicPtr, Ordering};

// ========================================================================
// Lean object layouts (needed for cast helpers below)
// ========================================================================

#[repr(C)]
pub struct lean_ctor_object {
    pub m_header: lean_object,
    pub m_objs: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_array_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_data: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_sarray_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_data: [u8; 0],
}

#[repr(C)]
pub struct lean_string_object {
    pub m_header: lean_object,
    pub m_size: size_t,
    pub m_capacity: size_t,
    pub m_length: size_t,
    pub m_data: [u8; 0],
}

#[repr(C)]
pub struct lean_closure_object {
    pub m_header: lean_object,
    pub m_fun: *mut c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    pub m_objs: [*mut lean_object; 0],
}

#[repr(C)]
pub struct lean_ref_object {
    pub m_header: lean_object,
    pub m_value: *mut lean_object,
}

#[repr(C)]
pub struct lean_thunk_object {
    pub m_header: lean_object,
    pub m_value: AtomicPtr<lean_object>,
    pub m_closure: AtomicPtr<lean_object>,
}

#[repr(C)]
pub struct lean_task_imp {
    pub m_closure: *mut lean_object,
    pub m_head_dep: *mut lean_task_object,
    pub m_next_dep: *mut lean_task_object,
    pub m_prio: u32,
    pub m_canceled: u8,
    pub m_keep_alive: u8,
    pub m_deleted: u8,
    pub _padding: u8,
}

#[repr(C)]
pub struct lean_task_object {
    pub m_header: lean_object,
    pub m_value: AtomicPtr<lean_object>,
    pub m_imp: *mut lean_task_imp,
}

#[repr(C)]
pub struct lean_promise_object {
    pub m_header: lean_object,
    pub m_result: *mut lean_task_object,
}

#[repr(C)]
pub struct lean_external_object {
    pub m_header: lean_object,
    pub m_class: *mut c_void,
    pub m_data: *mut c_void,
}

// ============================================================================
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

#[inline(always)]
unsafe fn lean_get_rc_mt_addr(o: *mut lean_object) -> *mut AtomicI32 {
    &mut (*o).m_rc as *mut _ as *mut AtomicI32
}

#[inline]
pub unsafe fn lean_inc_ref_n(o: *mut lean_object, n: size_t) {
    if lean_is_st(o) {
        (*o).m_rc = (*o).m_rc.wrapping_add(n as i32);
    } else if lean_is_mt(o) {
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
    if (*o).m_rc > 1 {
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
    if lean_is_st(o) {
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
// Natural Number Functions
// ============================================================================

const LEAN_MAX_SMALL_NAT: size_t = size_t::MAX >> 1;

/// Convert usize to Lean natural number.
///
/// For small numbers (< LEAN_MAX_SMALL_NAT), boxes them directly.
/// For large numbers, allocates a big nat object.
#[inline]
pub unsafe fn lean_usize_to_nat(n: size_t) -> lean_obj_res {
    if n <= LEAN_MAX_SMALL_NAT {
        lean_box(n)
    } else {
        // For big numbers, use lean_alloc_mpz
        lean_alloc_mpz(n)
    }
}

/// Convert Lean natural number to usize.
///
/// # Safety
/// - `o` must be a valid nat object
/// - Returns the unboxed value for scalars, calls big nat converter for heap nats
#[inline]
pub unsafe fn lean_usize_of_nat(o: b_lean_obj_arg) -> size_t {
    if lean_is_scalar(o) {
        lean_unbox(o)
    } else {
        lean_usize_of_big_nat(o)
    }
}

// External declarations for big nat functions
extern "C" {
    fn lean_alloc_mpz(n: size_t) -> lean_obj_res;
    fn lean_usize_of_big_nat(o: b_lean_obj_arg) -> size_t;
}

/// Get C string pointer from Lean string
#[inline]
pub unsafe fn lean_string_cstr(o: b_lean_obj_arg) -> *const libc::c_char {
    // The string data starts right after the lean_string_object header
    let str_obj = o as *const lean_string_object;
    let data_ptr = (str_obj as *const u8).add(std::mem::size_of::<lean_string_object>());
    data_ptr as *const libc::c_char
}

/// Get string length (number of UTF-8 characters)
#[inline]
pub unsafe fn lean_string_len(o: b_lean_obj_arg) -> size_t {
    let str_obj = o as *const lean_string_object;
    (*str_obj).m_length
}

/// Get string size in bytes (including null terminator)
#[inline]
pub unsafe fn lean_string_size(o: b_lean_obj_arg) -> size_t {
    let str_obj = o as *const lean_string_object;
    (*str_obj).m_size
}

// ============================================================================
// Array Functions (TODO: implement once struct definitions are available)
// ============================================================================

// These require lean_array_object struct definition - will add later

// ============================================================================
// Nat Arithmetic (static inline wrappers around exported functions)
// ============================================================================

/// Add two natural numbers.
///
/// # Safety
/// - Both arguments must be valid nat objects
#[inline]
pub unsafe fn lean_nat_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    // Check if both are small nats
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if let Some(sum) = n1.checked_add(n2) {
            if sum <= LEAN_MAX_SMALL_NAT {
                return lean_box(sum);
            }
        }
    }
    // Fall back to big nat addition
    lean_nat_big_add(a1, a2)
}

/// Subtract natural numbers.
///
/// # Safety
/// - Both arguments must be valid nat objects
#[inline]
pub unsafe fn lean_nat_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if n1 >= n2 {
            return lean_box(n1 - n2);
        }
    }
    lean_nat_big_sub(a1, a2)
}

/// Multiply two natural numbers.
///
/// # Safety
/// - Both arguments must be valid nat objects
#[inline]
pub unsafe fn lean_nat_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if let Some(product) = n1.checked_mul(n2) {
            if product <= LEAN_MAX_SMALL_NAT {
                return lean_box(product);
            }
        }
    }
    lean_nat_big_mul(a1, a2)
}

/// Divide natural numbers.
///
/// # Safety
/// - Both arguments must be valid nat objects
/// - `a2` must not be zero
#[inline]
pub unsafe fn lean_nat_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if n2 != 0 {
            return lean_box(n1 / n2);
        }
    }
    lean_nat_big_div(a1, a2)
}

/// Modulo operation.
///
/// # Safety
/// - Both arguments must be valid nat objects
/// - `a2` must not be zero
#[inline]
pub unsafe fn lean_nat_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        let n1 = lean_unbox(a1);
        let n2 = lean_unbox(a2);
        if n2 != 0 {
            return lean_box(n1 % n2);
        }
    }
    lean_nat_big_mod(a1, a2)
}

// Nat comparison functions
#[inline]
pub unsafe fn lean_nat_dec_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        a1 == a2
    } else {
        lean_nat_big_eq(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_dec_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_unbox(a1) < lean_unbox(a2)
    } else {
        lean_nat_big_lt(a1, a2)
    }
}

#[inline]
pub unsafe fn lean_nat_dec_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_unbox(a1) <= lean_unbox(a2)
    } else {
        lean_nat_big_le(a1, a2)
    }
}

// External declarations for big nat operations
extern "C" {
    fn lean_nat_big_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;
    fn lean_nat_big_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;
    fn lean_nat_big_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;
    fn lean_nat_big_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;
    fn lean_nat_big_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;
    fn lean_nat_big_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;
    fn lean_nat_big_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;
    fn lean_nat_big_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;
}
