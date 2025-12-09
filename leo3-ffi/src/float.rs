//! FFI bindings for Lean4 floating-point operations
//!
//! This module provides low-level bindings to Lean4's Float (64-bit) operations.

extern "C" {
    /// Check if a float is NaN
    pub fn lean_float_isnan(a: f64) -> u8;

    /// Check if a float is finite (not infinite and not NaN)
    pub fn lean_float_isfinite(a: f64) -> u8;

    /// Check if a float is infinite
    pub fn lean_float_isinf(a: f64) -> u8;

    /// Convert float to string
    pub fn lean_float_to_string(a: f64) -> *mut crate::lean_object;

    /// Scale a float by a power of 2
    pub fn lean_float_scaleb(a: f64, b: *const crate::lean_object) -> f64;

    /// Extract mantissa and exponent (frexp)
    pub fn lean_float_frexp(a: f64) -> *mut crate::lean_object;
}
