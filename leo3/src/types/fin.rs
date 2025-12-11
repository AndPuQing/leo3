//! Lean Fin (finite natural numbers) type wrapper.
//!
//! The `Fin n` type represents natural numbers less than `n`, forming a finite type with `n` elements.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanNat;

/// A Lean Fin (finite natural number) object.
///
/// Fin in Lean4 is defined as a structure:
/// ```lean
/// structure Fin (n : Nat) where
///   val : Nat
///   isLt : val < n
/// ```
///
/// `Fin n` represents the type of natural numbers strictly less than `n`.
/// It's the canonical n-element type, containing exactly the values `{0, 1, 2, ..., n-1}`.
///
/// # Runtime Representation
///
/// At runtime, only the natural number value is stored - the proof that `val < n` is erased.
/// This means `Fin n` has the same runtime representation as `Nat`: constructor 0 with 1 field.
///
/// # Modular Arithmetic
///
/// All arithmetic operations on `Fin n` are performed modulo `n`, wrapping around on overflow.
/// For example, in `Fin 3`:
/// - `2 + 1 = 0` (wraps around)
/// - `0 - 1 = 2` (wraps around)
///
/// # Use Cases
///
/// - Array/vector indexing with guaranteed bounds
/// - Modular arithmetic
/// - Representing fixed-size enumerations
pub struct LeanFin {
    _private: (),
}

impl LeanFin {
    /// Create a Fin from a Nat value with bounds checking.
    ///
    /// The value is taken modulo `bound` to ensure it's within range.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.ofNat` in Lean4:
    /// ```lean
    /// protected def ofNat (n : Nat) [NeZero n] (a : Nat) : Fin n :=
    ///   ⟨a % n, Nat.mod_lt _ (pos_of_neZero n)⟩
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let bound = LeanNat::from_usize(lean, 10)?;  // Fin 10
    ///     let value = LeanNat::from_usize(lean, 15)?;  // 15 % 10 = 5
    ///     let fin = LeanFin::ofNat(lean, &value, &bound)?;
    ///     Ok(())
    /// })
    /// ```
    #[allow(non_snake_case)]
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        value: LeanBound<'l, LeanNat>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // Calculate value % bound
        let modded = LeanNat::mod_(value, bound)?;

        unsafe {
            // Fin is constructor 0 with 1 field (the Nat value, proof erased)
            let ptr = ffi::lean_alloc_ctor(0, 1, 0);
            ffi::lean_ctor_set(ptr, 0, modded.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Fin directly from a Nat (assumes value is already < bound).
    ///
    /// # Safety
    ///
    /// This assumes the Lean code that created this value proved that `val < bound`.
    /// There is no runtime verification.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `Fin.mk` constructor.
    pub fn mk<'l>(
        lean: Lean<'l>,
        value: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 1, 0);
            ffi::lean_ctor_set(ptr, 0, value.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Extract the natural number value from a Fin.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.val` or `Fin.toNat` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let fin = LeanFin::ofNat(lean, &value, &bound)?;
    /// let nat_value = LeanFin::toNat(lean, &fin);
    /// ```
    #[allow(non_snake_case)]
    pub fn toNat<'l>(lean: Lean<'l>, obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanNat> {
        unsafe {
            let val_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(val_ptr);
            LeanBound::from_owned_ptr(lean, val_ptr)
        }
    }

    /// Addition modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.add` or the `+` operator in Lean4:
    /// ```lean
    /// protected def add : Fin n → Fin n → Fin n
    ///   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(a + b) % n, ..⟩
    /// ```
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // (2 : Fin 3) + (2 : Fin 3) = (1 : Fin 3)
    /// let a = LeanFin::ofNat(lean, &two, &three)?;
    /// let b = LeanFin::ofNat(lean, &two, &three)?;
    /// let sum = LeanFin::add(lean, &a, &b, &three)?;
    /// ```
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let sum = LeanNat::add(a_val, b_val)?;
        let modded = LeanNat::mod_(sum, bound)?;
        Self::mk(lean, modded)
    }

    /// Subtraction modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.sub` or the `-` operator in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // (3 : Fin 11) - (5 : Fin 11) = (9 : Fin 11)
    /// let a = LeanFin::ofNat(lean, &three, &eleven)?;
    /// let b = LeanFin::ofNat(lean, &five, &eleven)?;
    /// let diff = LeanFin::sub(lean, &a, &b, &eleven)?;
    /// ```
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);

        // First clone bound for later use in modulo
        let bound_clone = unsafe {
            ffi::lean_inc(bound.as_ptr());
            LeanBound::from_owned_ptr(lean, bound.as_ptr())
        };

        // Calculate (bound - b_val + a_val) % bound
        let bound_minus_b = LeanNat::sub(bound, b_val)?;
        let sum = LeanNat::add(bound_minus_b, a_val)?;
        let modded = LeanNat::mod_(sum, bound_clone)?;
        Self::mk(lean, modded)
    }

    /// Multiplication modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.mul` or the `*` operator in Lean4.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let product = LeanNat::mul(a_val, b_val)?;
        let modded = LeanNat::mod_(product, bound)?;
        Self::mk(lean, modded)
    }

    /// Division of bounded numbers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.div` or the `/` operator in Lean4.
    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let quotient = LeanNat::div(a_val, b_val)?;
        Self::mk(lean, quotient)
    }

    /// Modulus of bounded numbers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.mod` or the `%` operator in Lean4.
    pub fn modulo<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let remainder = LeanNat::mod_(a_val, b_val)?;
        Self::mk(lean, remainder)
    }

    /// Bitwise AND modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.land` in Lean4:
    /// ```lean
    /// def land : Fin n → Fin n → Fin n
    ///   | ⟨a, h⟩, ⟨b, _⟩ => ⟨(Nat.land a b) % n, ..⟩
    /// ```
    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::land(a_val, b_val)?;
        let modded = LeanNat::mod_(result, bound)?;
        Self::mk(lean, modded)
    }

    /// Bitwise OR modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.lor` in Lean4.
    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::lor(a_val, b_val)?;
        let modded = LeanNat::mod_(result, bound)?;
        Self::mk(lean, modded)
    }

    /// Bitwise XOR modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.xor` in Lean4.
    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::xor(a_val, b_val)?;
        let modded = LeanNat::mod_(result, bound)?;
        Self::mk(lean, modded)
    }

    /// Bitwise left shift modulo n.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.shiftLeft` or the `<<<` operator in Lean4.
    #[allow(non_snake_case)]
    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
        bound: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::shiftLeft(a_val, b_val)?;
        let modded = LeanNat::mod_(result, bound)?;
        Self::mk(lean, modded)
    }

    /// Bitwise right shift.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Fin.shiftRight` or the `>>>` operator in Lean4.
    #[allow(non_snake_case)]
    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let a_val = Self::toNat(lean, a);
        let b_val = Self::toNat(lean, b);
        let result = LeanNat::shiftRight(a_val, b_val)?;
        Self::mk(lean, result)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanFin> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanFin(...)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fin_size() {
        // Verify that LeanFin is zero-sized
        assert_eq!(std::mem::size_of::<LeanFin>(), 0);
    }
}
