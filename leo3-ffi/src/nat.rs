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
    /// Successor operation for big nat
    ///
    /// # Safety
    /// - `a` must be a valid nat object (consumed)
    pub fn lean_nat_big_succ(a: lean_obj_arg) -> lean_obj_res;

    /// Addition for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_add(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Subtraction for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_sub(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Multiplication for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_mul(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Handle overflow in nat multiplication
    ///
    /// # Safety
    /// - Called when multiplication would overflow small nat representation
    pub fn lean_nat_overflow_mul(a1: usize, a2: usize) -> lean_obj_res;

    /// Division for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_div(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Exact division for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_div_exact(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Modulus for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_mod(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Equality comparison for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_big_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Less-than-or-equal comparison for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_big_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Less-than comparison for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects
    pub fn lean_nat_big_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool;

    /// Bitwise AND for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_land(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Bitwise OR for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_lor(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Bitwise XOR for big nat
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    pub fn lean_nat_big_xor(a1: lean_obj_arg, a2: lean_obj_arg) -> lean_obj_res;

    /// Convert C string to nat
    ///
    /// # Safety
    /// - `n` must be a valid null-terminated string representing a number
    pub fn lean_cstr_to_nat(n: *const libc::c_char) -> lean_obj_res;

    /// Convert usize to bignat (for large values)
    ///
    /// # Safety
    /// - Always safe to call
    pub fn lean_big_usize_to_nat(n: usize) -> lean_obj_res;

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

    /// Extract usize from bignat object
    ///
    /// # Safety
    /// - `a` must be a valid nat object that is not scalar
    pub fn lean_usize_of_big_nat(a: b_lean_obj_arg) -> usize;

    // ============================================================================
    // Native Lean Nat functions (compiled from Lean stdlib)
    // Note: These are internal compiled functions and may not be stable across
    // Lean versions, but they provide optimized implementations.
    // ============================================================================

    /// Predecessor (native Lean implementation)
    ///
    /// # Safety
    /// - `n` must be a valid nat object (borrowed)
    #[link_name = "l_Nat_pred___boxed"]
    pub fn lean_nat_pred(n: b_lean_obj_arg) -> lean_obj_res;

    /// Min (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_min___boxed"]
    pub fn lean_nat_min(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Max (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_max___boxed"]
    pub fn lean_nat_max(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// LCM (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (consumed)
    #[link_name = "l_Nat_lcm___boxed"]
    pub fn lean_nat_lcm(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Bitwise left shift (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_shiftLeft___boxed"]
    pub fn lean_nat_shift_left(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Bitwise right shift (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_shiftRight___boxed"]
    pub fn lean_nat_shift_right(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Bitwise XOR (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_xor___boxed"]
    pub fn lean_nat_xor(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Bitwise OR (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_lor___boxed"]
    pub fn lean_nat_lor(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Bitwise AND (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    #[link_name = "l_Nat_land___boxed"]
    pub fn lean_nat_land(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Test bit (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    ///   Returns a Lean Bool object (must be decremented)
    #[link_name = "l_Nat_testBit___boxed"]
    pub fn lean_nat_test_bit(n: b_lean_obj_arg, i: b_lean_obj_arg) -> lean_obj_res;

    /// Boolean equality (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    ///   Returns a Lean Bool object (must be decremented)
    #[link_name = "l_Nat_beq___boxed"]
    pub fn lean_nat_beq(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Boolean less-than-or-equal (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    ///   Returns a Lean Bool object (must be decremented)
    #[link_name = "l_Nat_ble___boxed"]
    pub fn lean_nat_ble(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Boolean less-than (native Lean implementation)
    ///
    /// # Safety
    /// - Both arguments must be valid nat objects (borrowed)
    ///   Returns a Lean Bool object (must be decremented)
    #[link_name = "l_Nat_blt___boxed"]
    pub fn lean_nat_blt(a: b_lean_obj_arg, b: b_lean_obj_arg) -> lean_obj_res;

    /// Next power of two (native Lean implementation)
    ///
    /// # Safety
    /// - `n` must be a valid nat object (consumed)
    #[link_name = "l_Nat_nextPowerOfTwo___boxed"]
    pub fn lean_nat_next_power_of_two(n: lean_obj_arg) -> lean_obj_res;
}
