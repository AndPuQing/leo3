//! FFI bindings for Lean4 floating-point operations
//!
//! This module provides low-level bindings to Lean4's Float (64-bit) and Float32 (32-bit) operations.

extern "C" {
    // ========================================================================
    // Float (64-bit) operations
    // ========================================================================

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

    // ========================================================================
    // Float32 (32-bit) operations
    // ========================================================================

    /// Check if a float32 is NaN
    pub fn lean_float32_isnan(a: f32) -> u8;

    /// Check if a float32 is finite (not infinite and not NaN)
    pub fn lean_float32_isfinite(a: f32) -> u8;

    /// Check if a float32 is infinite
    pub fn lean_float32_isinf(a: f32) -> u8;

    /// Convert float32 to string
    pub fn lean_float32_to_string(a: f32) -> *mut crate::lean_object;

    /// Scale a float32 by a power of 2
    pub fn lean_float32_scaleb(a: f32, b: *const crate::lean_object) -> f32;

    /// Extract mantissa and exponent (frexp) for float32
    pub fn lean_float32_frexp(a: f32) -> *mut crate::lean_object;

    // ========================================================================
    // Float32 arithmetic operations
    // ========================================================================

    /// Add two float32 values
    pub fn lean_float32_add(a: f32, b: f32) -> f32;

    /// Subtract two float32 values
    pub fn lean_float32_sub(a: f32, b: f32) -> f32;

    /// Multiply two float32 values
    pub fn lean_float32_mul(a: f32, b: f32) -> f32;

    /// Divide two float32 values
    pub fn lean_float32_div(a: f32, b: f32) -> f32;

    /// Negate a float32 value
    pub fn lean_float32_negate(a: f32) -> f32;

    // ========================================================================
    // Float32 comparison operations
    // ========================================================================

    /// Float32 equality comparison
    pub fn lean_float32_beq(a: f32, b: f32) -> u8;

    /// Float32 decidable less than comparison
    pub fn lean_float32_decLt(a: f32, b: f32) -> u8;

    /// Float32 decidable less than or equal comparison
    pub fn lean_float32_decLe(a: f32, b: f32) -> u8;

    // ========================================================================
    // Float32 bits operations
    // ========================================================================

    /// Convert float32 to bits
    pub fn lean_float32_to_bits(d: f32) -> u32;

    /// Convert bits to float32
    pub fn lean_float32_of_bits(u: u32) -> f32;
}
