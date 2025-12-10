//! FFI bindings for Lean4 natural number operations
//!
//! Based on the nat functions from lean.h

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

/// Check if nat fits in usize (i.e., is a scalar)
///
/// # Safety
/// - `o` must be a valid nat object
#[inline]
pub unsafe fn leo3_nat_is_small(o: b_lean_obj_arg) -> bool {
    crate::inline::lean_is_scalar(o)
}

/// Shift right operation (wrapper that handles both small and big nats)
///
/// # Safety
/// - Both arguments must be valid nat objects (borrowed)
#[inline]
pub unsafe fn lean_nat_shiftr(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    use crate::inline::{lean_is_scalar, lean_unbox};

    if lean_is_scalar(a2) {
        let n2 = lean_unbox(a2);
        if lean_is_scalar(a1) {
            let n1 = lean_unbox(a1);
            return crate::inline::lean_box((n1 >> n2) as usize);
        }
    }
    lean_nat_big_shiftr(a1, a2)
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

    /// Log2 (logarithm base 2)
    ///
    /// # Safety
    /// - `a` must be a valid nat object (consumed)
    pub fn lean_nat_log2(a: b_lean_obj_arg) -> lean_obj_res;

    /// Bitwise AND
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_land(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Bitwise OR
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_lor(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Bitwise XOR
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_lxor(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Shift left
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_shiftl(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Shift right (for big nat)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_shiftr(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Convert uint64 to bignat (for values > LEAN_MAX_SMALL_NAT)
    ///
    /// # Safety
    /// - Always safe to call
    pub fn lean_big_uint64_to_nat(n: u64) -> lean_obj_res;

    /// Extract uint8 from bignat object
    ///
    /// # Safety
    /// - `a` must be a valid nat object that is not scalar
    pub fn lean_uint8_of_big_nat(a: b_lean_obj_arg) -> u8;

    /// Extract uint16 from bignat object
    ///
    /// # Safety
    /// - `a` must be a valid nat object that is not scalar
    pub fn lean_uint16_of_big_nat(a: b_lean_obj_arg) -> u16;

    /// Extract uint32 from bignat object
    ///
    /// # Safety
    /// - `a` must be a valid nat object that is not scalar
    pub fn lean_uint32_of_big_nat(a: b_lean_obj_arg) -> u32;

    /// Extract uint64 from bignat object
    ///
    /// # Safety
    /// - `a` must be a valid nat object that is not scalar
    pub fn lean_uint64_of_big_nat(a: b_lean_obj_arg) -> u64;

    /// Next power of two (native Lean implementation)
    ///
    /// Note: This is an internal Lean compiled function (l_Nat_nextPowerOfTwo___boxed)
    /// and may not be stable across Lean versions.
    ///
    /// # Safety
    /// - `n` must be a valid nat object (consumed)
    #[link_name = "l_Nat_nextPowerOfTwo___boxed"]
    pub fn lean_nat_next_power_of_two(n: lean_obj_arg) -> lean_obj_res;

}
