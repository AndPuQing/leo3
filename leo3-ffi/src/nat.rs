//! FFI bindings for Lean4 natural number operations
//!
//! Based on the nat functions from lean.h

use libc::size_t;
use crate::object::{lean_obj_arg, lean_obj_res, b_lean_obj_arg};

extern "C" {
    /// Convert usize to Lean natural number
    ///
    /// For small numbers, this boxes them directly.
    /// For large numbers, creates a GMP object.
    pub fn lean_usize_to_nat(n: size_t) -> lean_obj_res;

    /// Convert Lean natural number to usize
    ///
    /// # Safety
    /// - `o` must be a valid nat object
    /// - Result is undefined if the number doesn't fit in usize
    pub fn lean_nat_to_usize(o: b_lean_obj_arg) -> size_t;

    /// Check if nat fits in usize
    ///
    /// # Safety
    /// - `o` must be a valid nat object
    pub fn lean_nat_is_small(o: b_lean_obj_arg) -> bool;

    /// Add two natural numbers
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_add(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Subtract natural numbers (returns 0 if b > a)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_sub(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Multiply two natural numbers
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_mul(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Divide natural numbers
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    /// - `b` must not be zero
    pub fn lean_nat_div(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Modulo operation
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    /// - `b` must not be zero
    pub fn lean_nat_mod(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Compare natural numbers for equality
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_dec_eq(a: b_lean_obj_arg, b: b_lean_obj_arg) -> bool;

    /// Compare natural numbers for less-than
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_dec_lt(a: b_lean_obj_arg, b: b_lean_obj_arg) -> bool;

    /// Compare natural numbers for less-than-or-equal
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_dec_le(a: b_lean_obj_arg, b: b_lean_obj_arg) -> bool;

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
    crate::object::lean_box(n)
}

/// Convert natural number to boxed usize (if it fits)
///
/// # Safety
/// - `o` must be a valid nat object
/// - Panics if number doesn't fit in usize
#[inline]
pub unsafe fn lean_unbox_usize(o: b_lean_obj_arg) -> size_t {
    if crate::object::lean_is_scalar(o) {
        crate::object::lean_unbox(o)
    } else {
        // Large nat, try to convert
        if lean_nat_is_small(o) {
            lean_nat_to_usize(o)
        } else {
            panic!("Natural number too large for usize")
        }
    }
}
