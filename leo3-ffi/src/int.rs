//! FFI bindings for Lean4 integer operations
//!
//! This module provides low-level bindings to Lean4's integer (Int) type operations.
//! Lean integers support arbitrary precision for large values.

use crate::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

extern "C" {
    /// Convert a 64-bit signed integer to a Lean Int (for large values).
    ///
    /// This is called when the value doesn't fit in small int range.
    pub fn lean_big_int64_to_int(n: i64) -> lean_obj_res;

    /// Convert a size_t to a Lean Int (for large values).
    ///
    /// This is called when the value doesn't fit in small int range.
    pub fn lean_big_size_t_to_int(n: usize) -> lean_obj_res;

    /// Negate a large integer
    pub fn lean_int_big_neg(a: b_lean_obj_arg) -> lean_obj_res;

    /// Add two large integers
    pub fn lean_int_big_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Subtract two large integers
    pub fn lean_int_big_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Multiply two large integers
    pub fn lean_int_big_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Divide two large integers (truncated division)
    pub fn lean_int_big_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Exact division of two large integers
    pub fn lean_int_big_div_exact(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Modulus of two large integers
    pub fn lean_int_big_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Euclidean division of two large integers
    pub fn lean_int_big_ediv(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Euclidean modulus of two large integers
    pub fn lean_int_big_emod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res;

    /// Check equality of two large integers
    pub fn lean_int_big_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Check if first large integer is less than or equal to second
    pub fn lean_int_big_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Check if first large integer is less than second
    pub fn lean_int_big_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Check if a large integer is non-negative
    pub fn lean_int_big_nonneg(a: lean_obj_arg) -> bool;
}
