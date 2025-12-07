//! Rust re-implementations of Lean4's static inline functions
//!
//! Lean4's C API defines many functions as `static inline` in lean.h,
//! which means they don't exist as linkable symbols. Following PyO3's
//! approach, we manually re-implement these in Rust with #[inline] attributes.
//!
//! These implementations are based on Lean4 v4.25.2 headers.

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res, lean_object};
use libc::size_t;

// ============================================================================
// Core Object Functions
// ============================================================================

/// Check if an object is a scalar (immediate value, not a pointer).
///
/// Scalars have the lowest bit set to 1.
#[inline(always)]
pub unsafe fn lean_is_scalar(o: *const lean_object) -> bool {
    ((o as size_t) & 1) == 1
}

/// Box a size_t value into a scalar object.
///
/// Shifts left by 1 and sets the lowest bit to 1.
#[inline(always)]
pub unsafe fn lean_box(n: size_t) -> lean_obj_res {
    ((n << 1) | 1) as lean_obj_res
}

/// Unbox a scalar object to get the size_t value.
///
/// Shifts right by 1 to remove the tag bit.
#[inline(always)]
pub unsafe fn lean_unbox(o: b_lean_obj_arg) -> size_t {
    (o as size_t) >> 1
}

// ============================================================================
// Reference Counting
// ============================================================================

/// Check if an object uses single-threaded reference counting.
///
/// This checks if the object is not marked as multi-threaded.
/// Objects with m_rc > 0 are in ST mode, m_rc == 0 are persistent.
#[inline(always)]
unsafe fn lean_is_st(o: *mut lean_object) -> bool {
    // Don't dereference scalars
    if lean_is_scalar(o as *const lean_object) {
        return false;
    }
    // ST mode: m_rc > 0 (positive reference count)
    // MT mode: m_rc < 0 (negative means using atomic operations)
    // Persistent: m_rc == 0 (no reference counting needed)
    (*o).m_rc > 0
}

/// Increment reference count (without scalar check).
///
/// # Safety
/// - `o` must be a valid non-scalar object pointer
#[inline]
pub unsafe fn lean_inc_ref(o: *mut lean_object) {
    if lean_is_st(o) {
        (*o).m_rc = (*o).m_rc.wrapping_add(1);
    }
    // MT case would use atomic operations, but we're in ST mode for now
}

/// Decrement reference count (without scalar check).
///
/// # Safety
/// - `o` must be a valid non-scalar object pointer
/// - Calls lean_dec_ref_cold if count reaches 0
#[inline(always)]
pub unsafe fn lean_dec_ref(o: *mut lean_object) {
    if (*o).m_rc > 1 {
        (*o).m_rc -= 1;
    } else if (*o).m_rc != 0 {
        // Call the exported cold path for deallocation
        lean_dec_ref_cold(o);
    }
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

// External declaration for the cold path
extern "C" {
    fn lean_dec_ref_cold(o: *mut lean_object);
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

// ============================================================================
// String Functions
// ============================================================================

/// Lean string object layout (simplified)
#[repr(C)]
struct lean_string_object {
    m_header: lean_object,
    m_size: size_t,
    m_capacity: size_t,
    m_length: size_t,
    // m_data follows (flexible array member)
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
