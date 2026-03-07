//! Natural-number inline helpers.

use super::{
    likely,
    object::{lean_box, lean_is_scalar, lean_unbox},
};
use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};
use libc::size_t;

// Natural Number Functions
// ============================================================================

pub(crate) const LEAN_MAX_SMALL_NAT: size_t = size_t::MAX >> 1;

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

/// Successor of a natural number (inline from lean.h)
///
/// # Safety
/// - `a` must be a valid nat object
#[inline]
pub unsafe fn lean_nat_succ(a: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a)) {
        lean_usize_to_nat(lean_unbox(a) + 1)
    } else {
        crate::nat::lean_nat_big_succ(a as lean_obj_arg)
    }
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
        if let Some(result) = n1.checked_div(n2) {
            return lean_box(result);
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
