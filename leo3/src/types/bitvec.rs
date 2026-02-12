//! Lean BitVec (bitvector) type wrapper.
//!
//! The `BitVec w` type represents fixed-width bitvectors of width `w`.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanNat;

/// A Lean BitVec (bitvector) object.
///
/// BitVec in Lean4 is defined as a structure wrapping Fin:
/// ```lean
/// structure BitVec (w : Nat) where
///   ofFin :: toFin : Fin (2^w)
/// ```
///
/// `BitVec w` represents a fixed-width sequence of `w` bits, essentially a natural number
/// modulo `2^w`. It's used for efficient binary operations and bit manipulation.
///
/// # Runtime Representation
///
/// At runtime, BitVec has the same representation as Fin and Nat: constructor 0 with 1 field
/// containing a natural number. The width `w` is a type parameter, not stored at runtime.
///
/// The value is always less than `2^w`, maintained through modular arithmetic.
///
/// # Use Cases
///
/// - Low-level bit manipulation
/// - Hardware modeling
/// - Cryptographic operations
/// - Efficient fixed-width arithmetic
pub struct LeanBitVec {
    _private: (),
}

impl LeanBitVec {
    /// Create a BitVec from a natural number (taken modulo 2^width).
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.ofNat` in Lean4.
    ///
    /// # Parameters
    ///
    /// - `width`: The bit width
    /// - `value`: The natural number value (will be taken mod 2^width)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let value = LeanNat::from_usize(lean, 0b1010)?;
    ///     let width = LeanNat::from_usize(lean, 4)?;
    ///     let bv = LeanBitVec::ofNat(lean, width, value)?;
    ///     // Creates a 4-bit vector with value 10 (0b1010)
    ///     Ok(())
    /// })
    /// ```
    #[allow(non_snake_case)]
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        width: LeanBound<'l, LeanNat>,
        value: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // Calculate 2^width
        let two = LeanNat::from_usize(lean, 2)?;
        let bound = LeanNat::pow(two, width)?;

        // value % (2^width)
        let modded = LeanNat::mod_(value, bound)?;

        unsafe {
            let ptr = ffi::lean_mk_wrapper(modded.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Extract the natural number value from a BitVec.
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.toNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn toNat<'l>(lean: Lean<'l>, obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanNat> {
        unsafe {
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(val_ptr);
            LeanBound::from_owned_ptr(lean, val_ptr)
        }
    }

    /// Create a zero BitVec of the given width.
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.zero` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let width = LeanNat::from_usize(lean, 8)?;
    /// let zero_bv = LeanBitVec::zero(lean, width)?;
    /// // Creates 0b00000000
    /// ```
    pub fn zero<'l>(
        lean: Lean<'l>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let zero_val = LeanNat::from_usize(lean, 0)?;
        Self::ofNat(lean, width, zero_val)
    }

    /// Create a BitVec with all bits set to 1.
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.allOnes` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let width = LeanNat::from_usize(lean, 4)?;
    /// let all_ones = LeanBitVec::allOnes(lean, width)?;
    /// // Creates 0b1111 = 15
    /// ```
    #[allow(non_snake_case)]
    pub fn allOnes<'l>(
        lean: Lean<'l>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // 2^width - 1
        let width_clone = unsafe {
            ffi::lean_inc(width.as_ptr());
            LeanBound::from_owned_ptr(lean, width.as_ptr())
        };

        let two = LeanNat::from_usize(lean, 2)?;
        let pow = LeanNat::pow(two, width)?;
        let one = LeanNat::from_usize(lean, 1)?;
        let all_ones_val = LeanNat::sub(pow, one)?;

        Self::ofNat(lean, width_clone, all_ones_val)
    }

    /// Bitwise AND of two BitVecs.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `&&&` operator in Lean4.
    pub fn and<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::land(a_val, b_val)?;
        Self::ofNat(lean, width, result)
    }

    /// Bitwise OR of two BitVecs.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `|||` operator in Lean4.
    pub fn or<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::lor(a_val, b_val)?;
        Self::ofNat(lean, width, result)
    }

    /// Bitwise XOR of two BitVecs.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `^^^` operator in Lean4.
    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::xor(a_val, b_val)?;
        Self::ofNat(lean, width, result)
    }

    /// Bitwise NOT (complement).
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.not` or the `~~~` operator in Lean4.
    ///
    /// # Note
    ///
    /// The complement is width-dependent: `not` flips all bits within the width.
    /// For example, `not (0b1010 : BitVec 4) = 0b0101`.
    pub fn not<'l>(
        lean: Lean<'l>,
        obj: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // not(x) = allOnes XOR x
        let width_clone = unsafe {
            ffi::lean_inc(width.as_ptr());
            LeanBound::from_owned_ptr(lean, width.as_ptr())
        };

        let all_ones = Self::allOnes(lean, width)?;
        Self::xor(lean, &all_ones, obj, width_clone)
    }

    /// Addition modulo 2^width.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `+` operator for BitVec in Lean4.
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let sum = LeanNat::add(a_val, b_val)?;
        Self::ofNat(lean, width, sum)
    }

    /// Subtraction modulo 2^width.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `-` operator for BitVec in Lean4.
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);

        // Clone width for bound calculation
        let width_clone = unsafe {
            ffi::lean_inc(width.as_ptr());
            LeanBound::from_owned_ptr(lean, width.as_ptr())
        };

        // Calculate 2^width
        let two = LeanNat::from_usize(lean, 2)?;
        let bound = LeanNat::pow(two, width)?;

        // (bound + a - b) % bound
        let sum = LeanNat::add(bound, a_val)?;
        let diff = LeanNat::sub(sum, b_val)?;

        Self::ofNat(lean, width_clone, diff)
    }

    /// Multiplication modulo 2^width.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `*` operator for BitVec in Lean4.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let product = LeanNat::mul(a_val, b_val)?;
        Self::ofNat(lean, width, product)
    }

    /// Logical left shift.
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.shiftLeft` or the `<<<` operator in Lean4.
    #[allow(non_snake_case)]
    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        obj: &LeanBound<'l, Self>,
        n: &LeanBound<'l, LeanNat>,
        width: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = Self::toNat(lean, obj);
        let shifted = LeanNat::shiftLeft(val, unsafe {
            ffi::lean_inc(n.as_ptr());
            LeanBound::from_owned_ptr(lean, n.as_ptr())
        })?;
        Self::ofNat(lean, width, shifted)
    }

    /// Logical right shift.
    ///
    /// # Lean4 Reference
    /// Corresponds to `BitVec.shiftRight` or the `>>>` operator in Lean4.
    #[allow(non_snake_case)]
    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        obj: &LeanBound<'l, Self>,
        n: &LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = Self::toNat(lean, obj);
        let shifted = LeanNat::shiftRight(val, unsafe {
            ffi::lean_inc(n.as_ptr());
            LeanBound::from_owned_ptr(lean, n.as_ptr())
        })?;

        unsafe {
            let ptr = ffi::lean_mk_wrapper(shifted.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanBitVec> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanBitVec(...)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitvec_size() {
        // Verify that LeanBitVec is zero-sized
        assert_eq!(std::mem::size_of::<LeanBitVec>(), 0);
    }
}
