//! FFI bindings for Lean4 natural number operations
//!
//! Based on the nat functions from lean.h

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};
use libc::size_t;

// Re-export inline functions with leo3_ prefix for backwards compatibility
pub use crate::inline::{
    lean_nat_add as leo3_nat_add, lean_nat_dec_eq as leo3_nat_dec_eq,
    lean_nat_dec_le as leo3_nat_dec_le, lean_nat_dec_lt as leo3_nat_dec_lt,
    lean_nat_div as leo3_nat_div, lean_nat_mod as leo3_nat_mod, lean_nat_mul as leo3_nat_mul,
    lean_nat_sub as leo3_nat_sub, lean_usize_of_nat as leo3_nat_to_usize,
    lean_usize_to_nat as leo3_usize_to_nat,
};

/// Check if nat fits in usize (i.e., is a scalar)
///
/// # Safety
/// - `o` must be a valid nat object
#[inline]
pub unsafe fn leo3_nat_is_small(o: b_lean_obj_arg) -> bool {
    crate::inline::lean_is_scalar(o)
}

// These are actual exported functions from Lean4, not inline
extern "C" {
    /// Power operation
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_pow(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// GCD (Greatest Common Divisor)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_gcd(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;
}

// Inline helper functions

/// Convert boxed usize to natural number
///
/// This is typically already in the right format (boxed)
#[inline]
pub unsafe fn lean_box_usize(n: size_t) -> lean_obj_res {
    crate::inline::lean_box(n)
}

/// Convert natural number to boxed usize (if it fits)
///
/// # Safety
/// - `o` must be a valid nat object
/// - Panics if number doesn't fit in usize
#[inline]
pub unsafe fn lean_unbox_usize(o: b_lean_obj_arg) -> size_t {
    if crate::inline::lean_is_scalar(o) {
        crate::inline::lean_unbox(o)
    } else {
        // Large nat, try to convert
        if leo3_nat_is_small(o) {
            crate::inline::lean_usize_of_nat(o)
        } else {
            panic!("Natural number too large for usize")
        }
    }
}
