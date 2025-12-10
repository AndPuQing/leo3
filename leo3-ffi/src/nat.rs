//! FFI bindings for Lean4 natural number operations
//!
//! Based on the nat functions from lean.h

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};
use libc::size_t;

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
}

// Inline helper functions

/// Box a usize value into a Lean USize object
///
/// Note: USize in Lean is NOT the same as Nat. It's always a constructor
/// object (tag 0) with the size_t value stored in scalar data.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_box_usize(n: size_t) -> lean_obj_res {
    let r = crate::lean_alloc_ctor(0, 0, std::mem::size_of::<size_t>() as u32);
    crate::inline::lean_ctor_set_usize(r, 0, n);
    r
}

/// Unbox a Lean USize object to a size_t value
///
/// # Safety
/// - `o` must be a valid USize object (constructor with tag 0)
#[inline]
pub unsafe fn lean_unbox_usize(o: b_lean_obj_arg) -> size_t {
    crate::inline::lean_ctor_get_usize(o, 0)
}
