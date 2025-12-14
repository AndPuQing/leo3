//! Rust re-implementations of Lean4's static inline functions
//!
//! Lean4's C API defines many functions as `static inline` in lean.h,
//! which means they don't exist as linkable symbols. Following PyO3's
//! approach, we manually re-implement these in Rust with `#[inline]` attributes.
//!
//! These implementations are based on Lean4 v4.25.2 headers.

use crate::{
    object::{b_lean_obj_arg, b_lean_obj_res, lean_obj_arg, lean_obj_res, lean_object},
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
    lean_nat_big_add(a1 as lean_obj_arg, a2 as lean_obj_arg)
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
    lean_nat_big_sub(a1 as lean_obj_arg, a2 as lean_obj_arg)
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
    lean_nat_big_mul(a1 as lean_obj_arg, a2 as lean_obj_arg)
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
    lean_nat_big_div(a1 as lean_obj_arg, a2 as lean_obj_arg)
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
    lean_nat_big_mod(a1 as lean_obj_arg, a2 as lean_obj_arg)
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

// Import big nat operations from nat module
use crate::nat::{
    lean_nat_big_add, lean_nat_big_div, lean_nat_big_eq, lean_nat_big_le, lean_nat_big_lt,
    lean_nat_big_mod, lean_nat_big_mul, lean_nat_big_sub, lean_nat_big_xor,
};

/// Bitwise XOR for natural numbers
///
/// # Safety
/// - Both arguments must be valid nat objects (borrowed)
#[inline]
pub unsafe fn lean_nat_lxor(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a1) && lean_is_scalar(a2) {
        lean_box(lean_unbox(a1) ^ lean_unbox(a2))
    } else {
        lean_nat_big_xor(a1 as lean_obj_arg, a2 as lean_obj_arg)
    }
}

// ============================================================================
// Integer Functions
// ============================================================================

// Import the big int functions from the int module
use crate::int::{
    lean_big_int64_to_int, lean_big_size_t_to_int, lean_int_big_add, lean_int_big_div,
    lean_int_big_ediv, lean_int_big_emod, lean_int_big_eq, lean_int_big_le, lean_int_big_lt,
    lean_int_big_mod, lean_int_big_mul, lean_int_big_neg, lean_int_big_sub,
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
    if likely((LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT).contains(&n)) {
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

/// Convert a Lean Nat to a Lean Int.
///
/// This is the runtime implementation of `Int.ofNat`.
/// For small nats that fit in the small int range, returns the same pointer.
/// For larger values, converts to appropriate int representation.
///
/// # Safety
/// - `a` must be a valid Nat object (consumed)
#[inline]
pub unsafe fn lean_nat_to_int(a: lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a) {
        let v = lean_unbox(a);
        if v <= LEAN_MAX_SMALL_INT as usize {
            // Small nat that fits in small int range - return as-is
            a
        } else {
            // Nat is scalar but too large for small int - convert to big int
            lean_big_size_t_to_int(v)
        }
    } else {
        // Big nat - return as-is (big nat and big positive int have same representation)
        a
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

    lean_set_st_header(
        &mut (*o).m_header as *mut lean_object,
        LEAN_SCALAR_ARRAY,
        elem_size as u8,
    );

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

#[inline]
pub unsafe fn lean_float32_to_uint8(a: f32) -> u8 {
    if 0.0 <= a {
        if a < 256.0 {
            a as u8
        } else {
            u8::MAX
        }
    } else {
        0
    }
}

#[inline]
pub unsafe fn lean_float32_to_uint16(a: f32) -> u16 {
    if 0.0 <= a {
        if a < 65536.0 {
            a as u16
        } else {
            u16::MAX
        }
    } else {
        0
    }
}

/// Convert Float32 to UInt32
#[inline]
pub unsafe fn lean_float32_to_uint32(a: f32) -> u32 {
    if 0.0 <= a {
        if a < 4294967296.0 {
            a as u32
        } else {
            u32::MAX
        }
    } else {
        0
    }
}

/// Convert Float32 to UInt64
#[inline]
pub unsafe fn lean_float32_to_uint64(a: f32) -> u64 {
    if 0.0 <= a {
        if a < 18446744073709551616.0 {
            a as u64
        } else {
            u64::MAX
        }
    } else {
        0
    }
}

/// Convert Float32 to USize
#[inline]
pub unsafe fn lean_float32_to_usize(a: f32) -> usize {
    if std::mem::size_of::<usize>() == std::mem::size_of::<u64>() {
        lean_float32_to_uint64(a) as usize
    } else {
        lean_float32_to_uint32(a) as usize
    }
}

/// Convert Float32 to Int8
#[inline]
pub unsafe fn lean_float32_to_int8(a: f32) -> i8 {
    a as i8
}

/// Convert Float32 to Int16
#[inline]
pub unsafe fn lean_float32_to_int16(a: f32) -> i16 {
    a as i16
}

/// Convert Float32 to Int32
#[inline]
pub unsafe fn lean_float32_to_int32(a: f32) -> i32 {
    a as i32
}

/// Convert Float32 to Int64
#[inline]
pub unsafe fn lean_float32_to_int64(a: f32) -> i64 {
    a as i64
}

/// Convert Float32 to ISize
#[inline]
pub unsafe fn lean_float32_to_isize(a: f32) -> isize {
    a as isize
}

/// Convert UInt8 to Float32
#[inline]
pub unsafe fn lean_uint8_to_float32(a: u8) -> f32 {
    a as f32
}

/// Convert UInt16 to Float32
#[inline]
pub unsafe fn lean_uint16_to_float32(a: u16) -> f32 {
    a as f32
}

/// Convert UInt32 to Float32
#[inline]
pub unsafe fn lean_uint32_to_float32(a: u32) -> f32 {
    a as f32
}

/// Convert UInt64 to Float32
#[inline]
pub unsafe fn lean_uint64_to_float32(a: u64) -> f32 {
    a as f32
}

/// Convert USize to Float32
#[inline]
pub fn lean_usize_to_float32(a: usize) -> f32 {
    a as f32
}

/// Convert Int8 to Float32
#[inline]
pub unsafe fn lean_int8_to_float32(a: i8) -> f32 {
    a as f32
}

/// Convert Int16 to Float32
#[inline]
pub unsafe fn lean_int16_to_float32(a: i16) -> f32 {
    a as f32
}

/// Convert Int32 to Float32
#[inline]
pub unsafe fn lean_int32_to_float32(a: i32) -> f32 {
    a as f32
}

/// Convert Int64 to Float32
#[inline]
pub unsafe fn lean_int64_to_float32(a: i64) -> f32 {
    a as f32
}

/// Convert ISize to Float32
#[inline]
pub unsafe fn lean_isize_to_float32(a: isize) -> f32 {
    a as f32
}

/// Convert Float to Float32
#[inline]
pub unsafe fn lean_float_to_float32(a: f64) -> f32 {
    a as f32
}

/// Convert Float32 to Float
#[inline]
pub unsafe fn lean_float32_to_float(a: f32) -> f64 {
    a as f64
}

/// Convert Float to UInt8
#[inline]
pub unsafe fn lean_float_to_uint8(a: f64) -> u8 {
    a as u8
}

/// Convert Float to UInt16
#[inline]
pub unsafe fn lean_float_to_uint16(a: f64) -> u16 {
    a as u16
}

/// Convert Float to UInt32
#[inline]
pub unsafe fn lean_float_to_uint32(a: f64) -> u32 {
    a as u32
}

/// Convert Float to UInt64
#[inline]
pub unsafe fn lean_float_to_uint64(a: f64) -> u64 {
    a as u64
}

/// Convert Float to USize
#[inline]
pub unsafe fn lean_float_to_usize(a: f64) -> usize {
    a as usize
}

/// Convert Float to Int8
#[inline]
pub unsafe fn lean_float_to_int8(a: f64) -> i8 {
    a as i8
}

/// Convert Float to Int16
#[inline]
pub unsafe fn lean_float_to_int16(a: f64) -> i16 {
    a as i16
}

/// Convert Float to Int32
#[inline]
pub unsafe fn lean_float_to_int32(a: f64) -> i32 {
    a as i32
}

/// Convert Float to Int64
#[inline]
pub unsafe fn lean_float_to_int64(a: f64) -> i64 {
    a as i64
}

/// Convert Float to ISize
#[inline]
pub unsafe fn lean_float_to_isize(a: f64) -> isize {
    a as isize
}

/// Convert UInt8 to Float
#[inline]
pub unsafe fn lean_uint8_to_float(a: u8) -> f64 {
    a as f64
}

/// Convert UInt16 to Float
#[inline]
pub unsafe fn lean_uint16_to_float(a: u16) -> f64 {
    a as f64
}

/// Convert UInt32 to Float
#[inline]
pub unsafe fn lean_uint32_to_float(a: u32) -> f64 {
    a as f64
}

/// Convert UInt64 to Float
#[inline]
pub unsafe fn lean_uint64_to_float(a: u64) -> f64 {
    a as f64
}

/// Convert USize to Float
#[inline]
pub unsafe fn lean_usize_to_float(a: usize) -> f64 {
    a as f64
}

/// Convert Int8 to Float
#[inline]
pub unsafe fn lean_int8_to_float(a: i8) -> f64 {
    a as f64
}

/// Convert Int16 to Float
#[inline]
pub unsafe fn lean_int16_to_float(a: i16) -> f64 {
    a as f64
}

/// Convert Int32 to Float
#[inline]
pub unsafe fn lean_int32_to_float(a: i32) -> f64 {
    a as f64
}

/// Convert Int64 to Float
#[inline]
pub unsafe fn lean_int64_to_float(a: i64) -> f64 {
    a as f64
}

/// Convert ISize to Float
#[inline]
pub unsafe fn lean_isize_to_float(a: isize) -> f64 {
    a as f64
}

// UInt8 conversions
#[inline]
pub unsafe fn lean_uint8_to_uint16(a: u8) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint8_to_uint32(a: u8) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint8_to_uint64(a: u8) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint8_to_usize(a: u8) -> usize {
    a as usize
}

// UInt16 conversions
#[inline]
pub unsafe fn lean_uint16_to_uint8(a: u16) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint16_to_uint32(a: u16) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint16_to_uint64(a: u16) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint16_to_usize(a: u16) -> usize {
    a as usize
}

// UInt32 conversions
#[inline]
pub unsafe fn lean_uint32_to_uint8(a: u32) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint32_to_uint16(a: u32) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint32_to_uint64(a: u32) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint32_to_usize(a: u32) -> usize {
    a as usize
}

// UInt64 conversions
#[inline]
pub unsafe fn lean_uint64_to_uint8(a: u64) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint64_to_uint16(a: u64) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint64_to_uint32(a: u64) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint64_to_usize(a: u64) -> usize {
    a as usize
}

// USize conversions
#[inline]
pub unsafe fn lean_usize_to_uint8(a: usize) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_usize_to_uint16(a: usize) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_usize_to_uint32(a: usize) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_usize_to_uint64(a: usize) -> u64 {
    a as u64
}

// Int8 conversions
#[inline]
pub unsafe fn lean_int8_to_int16(a: u8) -> u16 {
    (a as i8 as i16) as u16
}

#[inline]
pub unsafe fn lean_int8_to_int32(a: u8) -> u32 {
    (a as i8 as i32) as u32
}

#[inline]
pub unsafe fn lean_int8_to_int64(a: u8) -> u64 {
    (a as i8 as i64) as u64
}

#[inline]
pub unsafe fn lean_int8_to_isize(a: u8) -> usize {
    (a as i8 as isize) as usize
}

// Int16 conversions
#[inline]
pub unsafe fn lean_int16_to_int8(a: u16) -> u8 {
    (a as i16 as i8) as u8
}

#[inline]
pub unsafe fn lean_int16_to_int32(a: u16) -> u32 {
    (a as i16 as i32) as u32
}

#[inline]
pub unsafe fn lean_int16_to_int64(a: u16) -> u64 {
    (a as i16 as i64) as u64
}

#[inline]
pub unsafe fn lean_int16_to_isize(a: u16) -> usize {
    (a as i16 as isize) as usize
}

// Int32 conversions
#[inline]
pub unsafe fn lean_int32_to_int8(a: u32) -> u8 {
    (a as i32 as i8) as u8
}

#[inline]
pub unsafe fn lean_int32_to_int16(a: u32) -> u16 {
    (a as i32 as i16) as u16
}

#[inline]
pub unsafe fn lean_int32_to_int64(a: u32) -> u64 {
    (a as i32 as i64) as u64
}

#[inline]
pub unsafe fn lean_int32_to_isize(a: u32) -> usize {
    (a as i32 as isize) as usize
}

// Int64 conversions
#[inline]
pub unsafe fn lean_int64_to_int8(a: u64) -> u8 {
    (a as i64 as i8) as u8
}

#[inline]
pub unsafe fn lean_int64_to_int16(a: u64) -> u16 {
    (a as i64 as i16) as u16
}

#[inline]
pub unsafe fn lean_int64_to_int32(a: u64) -> u32 {
    (a as i64 as i32) as u32
}

#[inline]
pub unsafe fn lean_int64_to_isize(a: u64) -> usize {
    (a as i64 as isize) as usize
}

// ISize conversions
#[inline]
pub unsafe fn lean_isize_to_int8(a: usize) -> u8 {
    (a as isize as i8) as u8
}

#[inline]
pub unsafe fn lean_isize_to_int16(a: usize) -> u16 {
    (a as isize as i16) as u16
}

#[inline]
pub unsafe fn lean_isize_to_int32(a: usize) -> u32 {
    (a as isize as i32) as u32
}

#[inline]
pub unsafe fn lean_isize_to_int64(a: usize) -> u64 {
    (a as isize as i64) as u64
}

/// Add two Float values
#[inline]
pub unsafe fn lean_float_add(a: f64, b: f64) -> f64 {
    a + b
}

/// Subtract two Float values
#[inline]
pub unsafe fn lean_float_sub(a: f64, b: f64) -> f64 {
    a - b
}

/// Multiply two Float values
#[inline]
pub unsafe fn lean_float_mul(a: f64, b: f64) -> f64 {
    a * b
}

/// Divide two Float values
#[inline]
pub unsafe fn lean_float_div(a: f64, b: f64) -> f64 {
    a / b
}

/// Negate a Float value
#[inline]
pub unsafe fn lean_float_negate(a: f64) -> f64 {
    -a
}

// ============================================================================
// Float comparison operations (static inline from lean.h)
// ============================================================================

/// Float equality comparison
#[inline]
pub unsafe fn lean_float_beq(a: f64, b: f64) -> u8 {
    (a == b) as u8
}

/// Float decidable less than or equal comparison
#[inline]
pub unsafe fn lean_float_decLe(a: f64, b: f64) -> u8 {
    (a <= b) as u8
}

/// Float decidable less than comparison
#[inline]
pub unsafe fn lean_float_decLt(a: f64, b: f64) -> u8 {
    (a < b) as u8
}

/// Add two Float32 values
#[inline]
pub unsafe fn lean_float32_add(a: f32, b: f32) -> f32 {
    a + b
}

/// Subtract two Float32 values
#[inline]
pub unsafe fn lean_float32_sub(a: f32, b: f32) -> f32 {
    a - b
}

/// Multiply two Float32 values
#[inline]
pub unsafe fn lean_float32_mul(a: f32, b: f32) -> f32 {
    a * b
}

/// Divide two Float32 values
#[inline]
pub unsafe fn lean_float32_div(a: f32, b: f32) -> f32 {
    a / b
}

/// Negate a Float32 value
#[inline]
pub unsafe fn lean_float32_negate(a: f32) -> f32 {
    -a
}

/// Float32 equality comparison
#[inline]
pub unsafe fn lean_float32_beq(a: f32, b: f32) -> u8 {
    (a == b) as u8
}

/// Float32 decidable less than or equal comparison
#[inline]
pub unsafe fn lean_float32_decLe(a: f32, b: f32) -> u8 {
    (a <= b) as u8
}

/// Float32 decidable less than comparison
#[inline]
pub unsafe fn lean_float32_decLt(a: f32, b: f32) -> u8 {
    (a < b) as u8
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

// --- UInt8 Operations ---

#[inline(always)]
pub unsafe fn lean_uint8_add(a1: u8, a2: u8) -> u8 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_sub(a1: u8, a2: u8) -> u8 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_mul(a1: u8, a2: u8) -> u8 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_div(a1: u8, a2: u8) -> u8 {
    if a2 == 0 {
        0
    } else {
        a1 / a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint8_mod(a1: u8, a2: u8) -> u8 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint8_land(a1: u8, a2: u8) -> u8 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint8_lor(a1: u8, a2: u8) -> u8 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint8_xor(a1: u8, a2: u8) -> u8 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint8_complement(a: u8) -> u8 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint8_shift_left(a1: u8, a2: u8) -> u8 {
    a1.wrapping_shl((a2 % 8) as u32)
}

#[inline(always)]
pub unsafe fn lean_uint8_shift_right(a1: u8, a2: u8) -> u8 {
    a1 >> (a2 % 8)
}

#[inline(always)]
pub unsafe fn lean_uint8_neg(a: u8) -> u8 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_eq(a1: u8, a2: u8) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_lt(a1: u8, a2: u8) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_le(a1: u8, a2: u8) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint8_log2(a: u8) -> u8 {
    if a == 0 {
        0
    } else {
        7 - a.leading_zeros() as u8
    }
}

// --- UInt16 Operations ---

#[inline(always)]
pub unsafe fn lean_uint16_add(a1: u16, a2: u16) -> u16 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_sub(a1: u16, a2: u16) -> u16 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_mul(a1: u16, a2: u16) -> u16 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_div(a1: u16, a2: u16) -> u16 {
    if a2 == 0 {
        0
    } else {
        a1 / a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint16_mod(a1: u16, a2: u16) -> u16 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint16_land(a1: u16, a2: u16) -> u16 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint16_lor(a1: u16, a2: u16) -> u16 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint16_xor(a1: u16, a2: u16) -> u16 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint16_complement(a: u16) -> u16 {
    !a
}
#[inline(always)]
pub unsafe fn lean_uint16_shift_left(a1: u16, a2: u16) -> u16 {
    let shift = (a2 & 0xF) as u32;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint16_shift_right(a1: u16, a2: u16) -> u16 {
    let shift = (a2 & 0xF) as u32;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint16_neg(a: u16) -> u16 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_eq(a1: u16, a2: u16) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_lt(a1: u16, a2: u16) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_le(a1: u16, a2: u16) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint16_log2(a: u16) -> u16 {
    if a == 0 {
        0
    } else {
        15 - a.leading_zeros() as u16
    }
}

// --- UInt32 Operations ---

#[inline(always)]
pub unsafe fn lean_uint32_add(a1: u32, a2: u32) -> u32 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_sub(a1: u32, a2: u32) -> u32 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_mul(a1: u32, a2: u32) -> u32 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_div(a1: u32, a2: u32) -> u32 {
    if a2 == 0 {
        0
    } else {
        a1 / a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint32_mod(a1: u32, a2: u32) -> u32 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint32_land(a1: u32, a2: u32) -> u32 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint32_lor(a1: u32, a2: u32) -> u32 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint32_xor(a1: u32, a2: u32) -> u32 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint32_complement(a: u32) -> u32 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint32_shift_left(a1: u32, a2: u32) -> u32 {
    let shift = a2 & 31;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint32_shift_right(a1: u32, a2: u32) -> u32 {
    let shift = a2 & 31;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint32_neg(a: u32) -> u32 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_eq(a1: u32, a2: u32) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_lt(a1: u32, a2: u32) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_le(a1: u32, a2: u32) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint32_is_valid_char(a: u32) -> bool {
    (a < 0xD800) || (0xE000..=0x10FFFF).contains(&a)
}

#[inline(always)]
pub unsafe fn lean_uint32_log2(a: u32) -> u32 {
    if a == 0 {
        0
    } else {
        31 - a.leading_zeros()
    }
}

// --- UInt64 Operations ---

#[inline(always)]
pub unsafe fn lean_uint64_add(a1: u64, a2: u64) -> u64 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_sub(a1: u64, a2: u64) -> u64 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_mul(a1: u64, a2: u64) -> u64 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_div(a1: u64, a2: u64) -> u64 {
    if a2 == 0 {
        0
    } else {
        a1 / a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_mod(a1: u64, a2: u64) -> u64 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_land(a1: u64, a2: u64) -> u64 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint64_lor(a1: u64, a2: u64) -> u64 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint64_xor(a1: u64, a2: u64) -> u64 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint64_complement(a: u64) -> u64 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint64_shift_left(a1: u64, a2: u64) -> u64 {
    let shift = (a2 & 63) as u32; // smod 64
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint64_shift_right(a1: u64, a2: u64) -> u64 {
    let shift = (a2 & 63) as u32; // smod 64
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint64_neg(a: u64) -> u64 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_eq(a1: u64, a2: u64) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_lt(a1: u64, a2: u64) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_le(a1: u64, a2: u64) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint64_log2(a: u64) -> u64 {
    if a == 0 {
        0
    } else {
        63 - a.leading_zeros() as u64
    }
}

// --- Conversion Functions: UInt to/from Nat ---

#[inline(always)]
pub unsafe fn lean_uint8_to_nat(a: u8) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint8_of_nat(a: *const lean_object) -> u8 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u8
    } else {
        crate::nat::lean_uint8_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint16_to_nat(a: u16) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint16_of_nat(a: *const lean_object) -> u16 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u16
    } else {
        crate::nat::lean_uint16_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint32_to_nat(a: u32) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint32_of_nat(a: *const lean_object) -> u32 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u32
    } else {
        crate::nat::lean_uint32_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_to_nat(n: u64) -> *mut lean_object {
    if n <= LEAN_MAX_SMALL_NAT as u64 {
        lean_box(n as usize)
    } else {
        crate::nat::lean_big_uint64_to_nat(n)
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_of_nat(a: *const lean_object) -> u64 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u64
    } else {
        crate::nat::lean_uint64_of_big_nat(a)
    }
}

// --- USize Operations ---

#[inline(always)]
pub unsafe fn lean_usize_add(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_sub(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_mul(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_div(a1: size_t, a2: size_t) -> size_t {
    if a2 == 0 {
        0
    } else {
        a1 / a2
    }
}

#[inline(always)]
pub unsafe fn lean_usize_mod(a1: size_t, a2: size_t) -> size_t {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_usize_land(a1: size_t, a2: size_t) -> size_t {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_usize_lor(a1: size_t, a2: size_t) -> size_t {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_usize_xor(a1: size_t, a2: size_t) -> size_t {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_usize_complement(a: size_t) -> size_t {
    !a
}

#[inline(always)]
pub unsafe fn lean_usize_shift_left(a1: size_t, a2: size_t) -> size_t {
    #[cfg(target_pointer_width = "64")]
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32;
    #[cfg(target_pointer_width = "32")]
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_usize_shift_right(a1: size_t, a2: size_t) -> size_t {
    #[cfg(target_pointer_width = "64")]
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32;
    #[cfg(target_pointer_width = "32")]
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_usize_neg(a: size_t) -> size_t {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_usize_dec_eq(a1: size_t, a2: size_t) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_usize_dec_lt(a1: size_t, a2: size_t) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_usize_dec_le(a1: size_t, a2: size_t) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_usize_log2(a: size_t) -> size_t {
    if a == 0 {
        0
    } else {
        (std::mem::size_of::<usize>() * 8 - 1) - a.leading_zeros() as usize
    }
}

#[inline(always)]
pub unsafe fn lean_int8_add(a1: u8, a2: u8) -> u8 {
    (a1 as i8).wrapping_add(a2 as i8) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_sub(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (lhs.wrapping_sub(rhs)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_mul(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (lhs.wrapping_mul(rhs)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_div(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_mod(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_land(a1: u8, a2: u8) -> u8 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int8_lor(a1: u8, a2: u8) -> u8 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int8_xor(a1: u8, a2: u8) -> u8 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int8_complement(a: u8) -> u8 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int8_shift_left(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let shift = (((a2 as i8 % 8) + 8) % 8) as u32; // smod 8
    (lhs.wrapping_shl(shift)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_shift_right(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let shift = (((a2 as i8 % 8) + 8) % 8) as u32; // smod 8
    (lhs.wrapping_shr(shift)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_neg(a: u8) -> u8 {
    let arg = a as i8;
    (arg.wrapping_neg()) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_abs(a: u8) -> u8 {
    let arg = a as i8;
    // With -fwrapv, INT8_MIN maps to INT8_MIN
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_dec_eq(a1: u8, a2: u8) -> bool {
    (a1 as i8) == (a2 as i8)
}

#[inline(always)]
pub unsafe fn lean_int8_dec_lt(a1: u8, a2: u8) -> bool {
    (a1 as i8) < (a2 as i8)
}

#[inline(always)]
pub unsafe fn lean_int8_dec_le(a1: u8, a2: u8) -> bool {
    (a1 as i8) <= (a2 as i8)
}

// --- Int16 Operations ---

#[inline(always)]
pub unsafe fn lean_int16_add(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_add(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_sub(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_sub(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_mul(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_mul(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_div(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_mod(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_land(a1: u16, a2: u16) -> u16 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int16_lor(a1: u16, a2: u16) -> u16 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int16_xor(a1: u16, a2: u16) -> u16 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int16_complement(a: u16) -> u16 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int16_shift_left(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let shift = (((a2 as i16 % 16) + 16) % 16) as u32; // smod 16
    (lhs.wrapping_shl(shift)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_shift_right(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let shift = (((a2 as i16 % 16) + 16) % 16) as u32; // smod 16
    (lhs.wrapping_shr(shift)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_neg(a: u16) -> u16 {
    let arg = a as i16;
    (arg.wrapping_neg()) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_abs(a: u16) -> u16 {
    let arg = a as i16;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_dec_eq(a1: u16, a2: u16) -> bool {
    (a1 as i16) == (a2 as i16)
}

#[inline(always)]
pub unsafe fn lean_int16_dec_lt(a1: u16, a2: u16) -> bool {
    (a1 as i16) < (a2 as i16)
}

#[inline(always)]
pub unsafe fn lean_int16_dec_le(a1: u16, a2: u16) -> bool {
    (a1 as i16) <= (a2 as i16)
}

// --- Int32 Operations ---

#[inline(always)]
pub unsafe fn lean_int32_add(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_add(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_sub(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_sub(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_mul(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_mul(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_div(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_mod(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_land(a1: u32, a2: u32) -> u32 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int32_lor(a1: u32, a2: u32) -> u32 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int32_xor(a1: u32, a2: u32) -> u32 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int32_complement(a: u32) -> u32 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int32_shift_left(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32; // smod 32
    (lhs.wrapping_shl(shift)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_shift_right(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32; // smod 32
    (lhs.wrapping_shr(shift)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_neg(a: u32) -> u32 {
    let arg = a as i32;
    (arg.wrapping_neg()) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_abs(a: u32) -> u32 {
    let arg = a as i32;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_dec_eq(a1: u32, a2: u32) -> bool {
    (a1 as i32) == (a2 as i32)
}

#[inline(always)]
pub unsafe fn lean_int32_dec_lt(a1: u32, a2: u32) -> bool {
    (a1 as i32) < (a2 as i32)
}

#[inline(always)]
pub unsafe fn lean_int32_dec_le(a1: u32, a2: u32) -> bool {
    (a1 as i32) <= (a2 as i32)
}

// --- Int64 Operations ---

#[inline(always)]
pub unsafe fn lean_int64_add(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_add(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_sub(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_sub(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_mul(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_mul(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_div(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_mod(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_land(a1: u64, a2: u64) -> u64 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int64_lor(a1: u64, a2: u64) -> u64 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int64_xor(a1: u64, a2: u64) -> u64 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int64_complement(a: u64) -> u64 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int64_shift_left(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32; // smod 64
    (lhs.wrapping_shl(shift)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_shift_right(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32; // smod 64
    (lhs.wrapping_shr(shift)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_neg(a: u64) -> u64 {
    let arg = a as i64;
    (arg.wrapping_neg()) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_abs(a: u64) -> u64 {
    let arg = a as i64;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_dec_eq(a1: u64, a2: u64) -> bool {
    (a1 as i64) == (a2 as i64)
}

#[inline(always)]
pub unsafe fn lean_int64_dec_lt(a1: u64, a2: u64) -> bool {
    (a1 as i64) < (a2 as i64)
}

#[inline(always)]
pub unsafe fn lean_int64_dec_le(a1: u64, a2: u64) -> bool {
    (a1 as i64) <= (a2 as i64)
}

// --- ISize Operations ---

#[inline(always)]
pub unsafe fn lean_isize_add(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_add(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_sub(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_sub(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_mul(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_mul(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_div(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (if rhs == 0 { 0 } else { lhs / rhs }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_mod(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (if rhs == 0 { lhs } else { lhs % rhs }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_land(a1: size_t, a2: size_t) -> size_t {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_isize_lor(a1: size_t, a2: size_t) -> size_t {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_isize_xor(a1: size_t, a2: size_t) -> size_t {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_isize_complement(a: size_t) -> size_t {
    !a
}

#[inline(always)]
pub unsafe fn lean_isize_shift_left(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    lhs.wrapping_shl(a2 as u32) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_shift_right(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    lhs.wrapping_shr(a2 as u32) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_neg(a: size_t) -> size_t {
    let arg = a as isize;
    (arg.wrapping_neg()) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_abs(a: size_t) -> size_t {
    let arg = a as isize;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_dec_eq(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) == (a2 as isize)
}

#[inline(always)]
pub unsafe fn lean_isize_dec_lt(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) < (a2 as isize)
}

#[inline(always)]
pub unsafe fn lean_isize_dec_le(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) <= (a2 as isize)
}

// ============================================================================
// External Object Functions
// ============================================================================

/// Allocate a small object (inline helper)
///
/// This is a simplified version that uses lean_alloc_object
#[inline(always)]
pub unsafe fn lean_alloc_small_object(sz: c_uint) -> *mut lean_object {
    use crate::object::lean_alloc_object;
    lean_alloc_object(sz as size_t)
}

/// Allocate an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_alloc_external(cls: *mut c_void, data: *mut c_void) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_external_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_EXTERNAL, 0);

    let ext = o as *mut lean_external_object;
    (*ext).m_class = cls;
    (*ext).m_data = data;

    o
}

/// Get the external class from an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_get_external_class(o: b_lean_obj_arg) -> *mut c_void {
    let ext = lean_to_external(o as lean_obj_arg);
    (*(ext as *const lean_external_object)).m_class
}

/// Get the data pointer from an external object (inline from lean.h)
#[inline(always)]
pub unsafe fn lean_get_external_data(o: b_lean_obj_arg) -> *mut c_void {
    (*(lean_to_external(o as lean_obj_arg) as *const lean_external_object)).m_data
}

// ============================================================================
// Task Inline Functions (from lean.h)
// ============================================================================

/// Spawn a task from a closure (inline wrapper around lean_task_spawn_core)
///
/// # Safety
/// - `c` must be a valid closure object (consumed)
/// - `prio` is the task priority (as a raw u32, not a Lean Nat object)
#[inline(always)]
pub unsafe fn lean_task_spawn(c: lean_obj_arg, prio: c_uint) -> lean_obj_res {
    crate::closure::lean_task_spawn_core(c, prio, false)
}

/// Get owned task result (inline from lean.h)
///
/// This is an inline function in Lean headers that wraps lean_task_get.
///
/// # Safety
/// - `t` must be a valid task object (consumed)
#[inline(always)]
pub unsafe fn lean_task_get_own(t: lean_obj_arg) -> lean_obj_res {
    let r = crate::closure::lean_task_get(t) as lean_obj_res;
    lean_inc(r);
    lean_dec(t);
    r
}

/// Map a function over a task (inline wrapper around lean_task_map_core)
///
/// # Safety
/// - `f` must be a valid closure object (consumed)
/// - `t` must be a valid task object (consumed)
/// - `prio` is the priority for the new task
/// - `sync` indicates if the task should be forced synchronously
#[inline(always)]
pub unsafe fn lean_task_map(
    f: lean_obj_arg,
    t: lean_obj_arg,
    prio: c_uint,
    sync: bool,
) -> lean_obj_res {
    crate::closure::lean_task_map_core(f, t, prio, sync, false)
}

/// Bind a function over a task (inline wrapper around lean_task_bind_core)
///
/// # Safety
/// - `x` must be a valid task object (consumed)
/// - `f` must be a valid closure object (consumed)
/// - `prio` is the priority for the new task
/// - `sync` indicates if the task should be forced synchronously
#[inline(always)]
pub unsafe fn lean_task_bind(
    x: lean_obj_arg,
    f: lean_obj_arg,
    prio: c_uint,
    sync: bool,
) -> lean_obj_res {
    crate::closure::lean_task_bind_core(x, f, prio, sync, false)
}

// ============================================================================
// Thunk Inline Functions (from lean.h)
// ============================================================================

extern "C" {
    /// Core thunk evaluation function (exported from libleanshared)
    ///
    /// This is the only thunk function exported from libleanshared.so.
    /// All other thunk functions are static inline in lean.h and must
    /// be reimplemented in Rust.
    pub fn lean_thunk_get_core(t: *mut lean_object) -> *mut lean_object;
}

/// Create a new thunk from a closure (inline from lean.h)
///
/// # Safety
/// - `c` must be a valid closure object (consumed)
#[inline(always)]
pub unsafe fn lean_mk_thunk(c: lean_obj_arg) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_thunk_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_THUNK, 0);

    let thunk = o as *mut lean_thunk_object;
    // Use atomic stores for consistency with lean_thunk_object definition
    (*thunk)
        .m_value
        .store(std::ptr::null_mut(), Ordering::Relaxed);
    (*thunk).m_closure.store(c, Ordering::Relaxed);

    o
}

/// Create a pure thunk that is already evaluated (inline from lean.h)
///
/// Thunk.pure : A -> Thunk A
///
/// # Safety
/// - `v` must be a valid lean object (consumed)
#[inline(always)]
pub unsafe fn lean_thunk_pure(v: lean_obj_arg) -> lean_obj_res {
    let o = lean_alloc_small_object(std::mem::size_of::<lean_thunk_object>() as c_uint);
    lean_set_st_header(o, crate::LEAN_THUNK, 0);

    let thunk = o as *mut lean_thunk_object;
    // Use atomic stores for consistency with lean_thunk_object definition
    (*thunk).m_value.store(v, Ordering::Relaxed);
    (*thunk)
        .m_closure
        .store(std::ptr::null_mut(), Ordering::Relaxed);

    o
}

/// Get the value from a thunk, forcing evaluation if needed (inline from lean.h)
///
/// # Safety
/// - `t` must be a valid thunk object (borrowed)
#[inline(always)]
pub unsafe fn lean_thunk_get(t: b_lean_obj_arg) -> b_lean_obj_res {
    let thunk = lean_to_thunk(t as lean_obj_arg);
    // Use atomic load for consistency
    let r = (*thunk).m_value.load(Ordering::Acquire);
    if !r.is_null() {
        r as b_lean_obj_res
    } else {
        lean_thunk_get_core(t as *mut lean_object) as b_lean_obj_res
    }
}

/// Get owned value from a thunk (inline from lean.h)
///
/// Primitive for implementing Thunk.get : Thunk A -> A
///
/// # Safety
/// - `t` must be a valid thunk object (borrowed)
#[inline(always)]
pub unsafe fn lean_thunk_get_own(t: b_lean_obj_arg) -> lean_obj_res {
    let r = lean_thunk_get(t);
    lean_inc(r as lean_obj_arg);
    r as lean_obj_res
}
