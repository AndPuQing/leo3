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
use libc::{c_uint, c_void, size_t};
use std::sync::atomic::{AtomicI32, AtomicPtr, Ordering};

// ========================================================================
// Branch Prediction Hints (corresponding to Lean's LEAN_LIKELY)
// ========================================================================

/// Hint to compiler that condition is likely to be true
#[inline(always)]
#[allow(dead_code)]
const fn likely(b: bool) -> bool {
    // In stable Rust, we can't use intrinsics, so this is a no-op
    // The compiler's own branch prediction is usually good enough
    // If you're on nightly, you could use: core::intrinsics::likely(b)
    b
}

/// Hint to compiler that condition is unlikely to be true
#[inline(always)]
#[allow(dead_code)]
const fn unlikely(b: bool) -> bool {
    // In stable Rust, we can't use intrinsics, so this is a no-op
    // If you're on nightly, you could use: core::intrinsics::unlikely(b)
    b
}

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
    (*lean_to_ctor(o)).m_objs.as_mut_ptr()
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
    if likely(n <= LEAN_MAX_SMALL_NAT) {
        lean_box(n)
    } else {
        // For big numbers, use lean_big_usize_to_nat
        lean_big_usize_to_nat(n)
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
    fn lean_big_usize_to_nat(n: size_t) -> lean_obj_res;
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
#[inline(always)]
pub unsafe fn lean_nat_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    // Check if both are small nats
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
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
#[inline(always)]
pub unsafe fn lean_nat_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
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
#[inline(always)]
pub unsafe fn lean_nat_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
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

// ============================================================================
// Integer Functions
// ============================================================================

// Import the big int functions from the int module
use crate::int::{
    lean_big_int64_to_int, lean_int_big_add, lean_int_big_div, lean_int_big_ediv,
    lean_int_big_emod, lean_int_big_eq, lean_int_big_le, lean_int_big_lt, lean_int_big_mod,
    lean_int_big_mul, lean_int_big_neg, lean_int_big_sub,
};

// Constants for small int range
const LEAN_MAX_SMALL_INT: i64 = if std::mem::size_of::<*const ()>() == 8 {
    i32::MAX as i64
} else {
    (i32::MAX >> 1) as i64
};

const LEAN_MIN_SMALL_INT: i64 = if std::mem::size_of::<*const ()>() == 8 {
    i32::MIN as i64
} else {
    (i32::MIN >> 1) as i64
};

/// Convert i64 to Lean Int.
///
/// For small integers (within LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT),
/// boxes them directly. For large integers, allocates a big int object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_int64_to_int(n: i64) -> lean_obj_res {
    if likely(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT) {
        lean_box(n as usize)
    } else {
        lean_big_int64_to_int(n)
    }
}

/// Convert scalar Int to i64.
///
/// # Safety
/// - `a` must be a scalar Int
#[inline]
pub unsafe fn lean_scalar_to_int64(a: b_lean_obj_arg) -> i64 {
    debug_assert!(lean_is_scalar(a));
    if std::mem::size_of::<*const ()>() == 8 {
        lean_unbox(a) as i32 as i64
    } else {
        ((a as isize) >> 1) as i64
    }
}

/// Convert scalar Int to i32.
///
/// # Safety
/// - `a` must be a scalar Int
#[inline]
pub unsafe fn lean_scalar_to_int(a: b_lean_obj_arg) -> i32 {
    debug_assert!(lean_is_scalar(a));
    if std::mem::size_of::<*const ()>() == 8 {
        lean_unbox(a) as i32
    } else {
        ((a as isize) >> 1) as i32
    }
}

/// Negate an integer.
///
/// # Safety
/// - `a` must be a valid Int object
#[inline]
pub unsafe fn lean_int_neg(a: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a)) {
        lean_int64_to_int(-lean_scalar_to_int64(a))
    } else {
        lean_int_big_neg(a)
    }
}

/// Add two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2))
    } else {
        lean_int_big_add(a1, a2)
    }
}

/// Subtract two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2))
    } else {
        lean_int_big_sub(a1, a2)
    }
}

/// Multiply two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2))
    } else {
        lean_int_big_mul(a1, a2)
    }
}

/// Divide two integers (truncated division).
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns 0 if dividing by zero
#[inline]
pub unsafe fn lean_int_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let v1 = lean_scalar_to_int(a1) as i64;
            let v2 = lean_scalar_to_int(a2) as i64;
            if v2 == 0 {
                lean_box(0)
            } else {
                lean_int64_to_int(v1 / v2)
            }
        } else {
            let v1 = lean_scalar_to_int(a1);
            let v2 = lean_scalar_to_int(a2);
            if v2 == 0 {
                lean_box(0)
            } else {
                lean_int64_to_int((v1 / v2) as i64)
            }
        }
    } else {
        lean_int_big_div(a1, a2)
    }
}

/// Modulus of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns a1 if dividing by zero
#[inline]
pub unsafe fn lean_int_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let v1 = lean_scalar_to_int64(a1);
            let v2 = lean_scalar_to_int64(a2);
            if v2 == 0 {
                a1 as lean_obj_res
            } else {
                lean_int64_to_int(v1 % v2)
            }
        } else {
            let v1 = lean_scalar_to_int(a1);
            let v2 = lean_scalar_to_int(a2);
            if v2 == 0 {
                a1 as lean_obj_res
            } else {
                lean_int64_to_int((v1 % v2) as i64)
            }
        }
    } else {
        lean_int_big_mod(a1, a2)
    }
}

/// Euclidean division of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns 0 if dividing by zero
#[inline]
pub unsafe fn lean_int_ediv(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let n = lean_scalar_to_int(a1) as i64;
            let d = lean_scalar_to_int(a2) as i64;
            if d == 0 {
                lean_box(0)
            } else {
                let q = n / d;
                let r = n % d;
                if (r > 0 && d < 0) || (r < 0 && d > 0) {
                    lean_int64_to_int(q - 1)
                } else {
                    lean_int64_to_int(q)
                }
            }
        } else {
            let n = lean_scalar_to_int(a1);
            let d = lean_scalar_to_int(a2);
            if d == 0 {
                lean_box(0)
            } else {
                let q = n / d;
                let r = n % d;
                if (r > 0 && d < 0) || (r < 0 && d > 0) {
                    lean_int64_to_int((q - 1) as i64)
                } else {
                    lean_int64_to_int(q as i64)
                }
            }
        }
    } else {
        lean_int_big_ediv(a1, a2)
    }
}

/// Euclidean modulus of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns a1 if dividing by zero
#[inline]
pub unsafe fn lean_int_emod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let n = lean_scalar_to_int64(a1);
            let d = lean_scalar_to_int64(a2);
            if d == 0 {
                a1 as lean_obj_res
            } else {
                let r = n % d;
                if r < 0 {
                    if d > 0 {
                        lean_int64_to_int(r + d)
                    } else {
                        lean_int64_to_int(r - d)
                    }
                } else if r == 0 {
                    lean_box(0)
                } else if d < 0 {
                    lean_int64_to_int(r + d)
                } else {
                    lean_int64_to_int(r)
                }
            }
        } else {
            let n = lean_scalar_to_int(a1) as i64;
            let d = lean_scalar_to_int(a2) as i64;
            if d == 0 {
                a1 as lean_obj_res
            } else {
                let r = n % d;
                if r < 0 {
                    if d > 0 {
                        lean_int64_to_int(r + d)
                    } else {
                        lean_int64_to_int(r - d)
                    }
                } else if r == 0 {
                    lean_box(0)
                } else if d < 0 {
                    lean_int64_to_int(r + d)
                } else {
                    lean_int64_to_int(r)
                }
            }
        }
    } else {
        lean_int_big_emod(a1, a2)
    }
}

/// Check equality of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        a1 == a2
    } else {
        lean_int_big_eq(a1, a2)
    }
}

/// Check if first integer is less than or equal to second.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_scalar_to_int(a1) <= lean_scalar_to_int(a2)
    } else {
        lean_int_big_le(a1, a2)
    }
}

/// Check if first integer is less than second.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_scalar_to_int(a1) < lean_scalar_to_int(a2)
    } else {
        lean_int_big_lt(a1, a2)
    }
}

// ============================================================================
// Float Functions
// ============================================================================

/// Box a double into a Lean Float object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_box_float(v: f64) -> lean_obj_res {
    let o = crate::lean_alloc_ctor(0, 0, 8); // tag 0, no objects, 8 bytes scalar
    *(o as *mut f64) = v;
    o
}

/// Unbox a Lean Float object to a double.
///
/// # Safety
/// - `o` must be a valid Float object
#[inline]
pub unsafe fn lean_unbox_float(o: b_lean_obj_arg) -> f64 {
    *(o as *const f64)
}

// ============================================================================
// Constructor Scalar Field Accessors (from lean.h)
// ============================================================================

/// Get uint8 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid within scalar area
#[inline]
pub unsafe fn lean_ctor_get_uint8(o: b_lean_obj_arg, offset: c_uint) -> u8 {
    *lean_ctor_scalar_cptr(o as *mut lean_object).add(offset as usize)
}

/// Set uint8 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid within scalar area
#[inline]
pub unsafe fn lean_ctor_set_uint8(o: lean_obj_arg, offset: c_uint, v: u8) {
    *lean_ctor_scalar_cptr(o).add(offset as usize) = v;
}

/// Get uint16 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 2-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint16(o: b_lean_obj_arg, offset: c_uint) -> u16 {
    *(lean_ctor_scalar_cptr(o as *mut lean_object).add(offset as usize) as *const u16)
}

/// Set uint16 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 2-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint16(o: lean_obj_arg, offset: c_uint, v: u16) {
    *(lean_ctor_scalar_cptr(o).add(offset as usize) as *mut u16) = v;
}

/// Get uint32 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 4-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint32(o: b_lean_obj_arg, offset: c_uint) -> u32 {
    *(lean_ctor_scalar_cptr(o as *mut lean_object).add(offset as usize) as *const u32)
}

/// Set uint32 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 4-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint32(o: lean_obj_arg, offset: c_uint, v: u32) {
    *(lean_ctor_scalar_cptr(o).add(offset as usize) as *mut u32) = v;
}

/// Get uint64 scalar from constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 8-byte aligned
#[inline]
pub unsafe fn lean_ctor_get_uint64(o: b_lean_obj_arg, offset: c_uint) -> u64 {
    *(lean_ctor_scalar_cptr(o as *mut lean_object).add(offset as usize) as *const u64)
}

/// Set uint64 scalar in constructor
///
/// # Safety
/// - `o` must be a valid constructor object
/// - `offset` must be valid and 8-byte aligned
#[inline]
pub unsafe fn lean_ctor_set_uint64(o: lean_obj_arg, offset: c_uint, v: u64) {
    *(lean_ctor_scalar_cptr(o).add(offset as usize) as *mut u64) = v;
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

// ============================================================================
// ByteArray Functions
// ============================================================================

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
    let o = crate::object::lean_alloc_object(total_size) as *mut lean_sarray_object;

    // Initialize header (matching lean_set_st_header from lean.h)
    (*o).m_header.m_rc = 1;
    (*o).m_header.m_tag = LEAN_SCALAR_ARRAY;
    (*o).m_header.m_other = elem_size as u8;
    (*o).m_header.m_cs_sz = 0;

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

/// Box a float (f32) into a Lean Float32 object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_box_float32(v: f32) -> lean_obj_res {
    let o = crate::lean_alloc_ctor(0, 0, 4); // tag 0, no objects, 4 bytes scalar
    *(o as *mut f32) = v;
    o
}

/// Unbox a Lean Float32 object to a float.
///
/// # Safety
/// - `o` must be a valid Float32 object
#[inline]
pub unsafe fn lean_unbox_float32(o: b_lean_obj_arg) -> f32 {
    *(o as *const f32)
}

// ============================================================================
// Scalar Array (ByteArray) Functions
// ============================================================================

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
    let sarray = o as *mut lean_sarray_object;
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
