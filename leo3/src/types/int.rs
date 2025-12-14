//! Lean integer type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanNat;

/// A Lean integer object.
///
/// Integers in Lean4 are inductively defined:
/// ```lean
/// inductive Int : Type where
///   | ofNat   : Nat → Int     -- non-negative integers
///   | negSucc : Nat → Int     -- negative integers
/// ```
///
/// The runtime has a special representation for `Int` that stores "small" signed
/// numbers directly, while larger numbers use a fast arbitrary-precision arithmetic
/// library (usually GMP).
pub struct LeanInt {
    _private: (),
}

impl LeanInt {
    /// Create a Lean integer from an i64.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.ofNat` for non-negative values or
    /// `Int.negSucc` for negative values.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let pos = LeanInt::from_i64(lean, 42)?;
    ///     let neg = LeanInt::from_i64(lean, -100)?;
    ///     assert_eq!(LeanInt::to_i64(&pos), Some(42));
    ///     assert_eq!(LeanInt::to_i64(&neg), Some(-100));
    ///     Ok(())
    /// })
    /// ```
    pub fn from_i64<'l>(lean: Lean<'l>, value: i64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::inline::lean_int64_to_int(value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Lean integer from an isize.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.ofNat` for non-negative values or
    /// `Int.negSucc` for negative values.
    pub fn from_isize<'l>(lean: Lean<'l>, value: isize) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_i64(lean, value as i64)
    }

    /// Create a Lean integer from a Lean natural number.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.ofNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::inline::lean_nat_to_int(nat.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Lean integer from zero.
    ///
    /// # Lean4 Reference
    /// Corresponds to `(0 : Int)` in Lean4.
    pub fn zero<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_i64(lean, 0)
    }

    /// Create a Lean integer from one.
    ///
    /// # Lean4 Reference
    /// Corresponds to `(1 : Int)` in Lean4.
    pub fn one<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_i64(lean, 1)
    }

    /// Convert a Lean integer to an i64 if it fits.
    ///
    /// Returns `None` if the integer is too large to fit in an i64.
    ///
    /// # Lean4 Reference
    /// Similar to `Int.toNat` followed by conversion to i64.
    pub fn to_i64<'l>(obj: &LeanBound<'l, Self>) -> Option<i64> {
        unsafe {
            if ffi::lean_is_scalar(obj.as_ptr()) {
                // Small integer stored as scalar
                Some(ffi::inline::lean_scalar_to_int64(obj.as_ptr()))
            } else {
                // Large integer - for now we only handle small integers
                // TODO: Add support for converting large integers
                None
            }
        }
    }

    /// Convert a Lean integer to an isize if it fits.
    ///
    /// Returns `None` if the integer is too large to fit in an isize.
    pub fn to_isize<'l>(obj: &LeanBound<'l, Self>) -> Option<isize> {
        Self::to_i64(obj).and_then(|v| {
            if v >= isize::MIN as i64 && v <= isize::MAX as i64 {
                Some(v as isize)
            } else {
                None
            }
        })
    }

    /// Check if the integer is non-negative (>= 0).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.NonNeg` or `0 ≤ x` in Lean4.
    #[allow(non_snake_case)]
    pub fn isNonNeg<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            if ffi::lean_is_scalar(obj.as_ptr()) {
                ffi::inline::lean_scalar_to_int64(obj.as_ptr()) >= 0
            } else {
                // Check if it's an ofNat constructor (tag 0)
                ffi::lean_obj_tag(obj.as_ptr()) == 0
            }
        }
    }

    /// Negate the integer.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.neg` or `-x` in Lean4.
    pub fn neg<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_neg(obj.as_ptr());
            // Need to decrement the reference of the input since lean_int_neg borrows
            ffi::lean_dec(obj.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Add two integers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.add` or `+` operator in Lean4.
    pub fn add<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_add(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Subtract two integers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.sub` or `-` operator in Lean4.
    pub fn sub<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_sub(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Multiply two integers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.mul` or `*` operator in Lean4.
    pub fn mul<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_mul(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Divide two integers (truncated division).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.div` or `/` operator in Lean4.
    ///
    /// # Panics
    /// Panics if dividing by zero.
    pub fn div<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_div(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Modulus operation.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.mod` or `%` operator in Lean4.
    ///
    /// # Panics
    /// Panics if dividing by zero.
    pub fn mod_<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_mod(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Euclidean division.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.ediv` in Lean4.
    pub fn ediv<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_ediv(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Euclidean modulus.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.emod` in Lean4.
    pub fn emod<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = a.lean_token();
        unsafe {
            let ptr = ffi::inline::lean_int_emod(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check equality of two integers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.beq` or `==` in Lean4.
    pub fn eq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_int_eq(a.as_ptr(), b.as_ptr()) }
    }

    /// Check if first integer is less than or equal to second.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.le` or `≤` in Lean4.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_int_le(a.as_ptr(), b.as_ptr()) }
    }

    /// Check if first integer is less than second.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.lt` or `<` in Lean4.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_int_lt(a.as_ptr(), b.as_ptr()) }
    }

    /// Decidable equality.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.decEq` in Lean4.
    #[allow(non_snake_case)]
    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::eq(a, b)
    }

    /// Get the sign of the integer.
    ///
    /// Returns 1 for positive, -1 for negative, 0 for zero.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.sign` in Lean4.
    pub fn sign<'l>(obj: &LeanBound<'l, Self>) -> i32 {
        match Self::to_i64(obj) {
            Some(v) if v > 0 => 1,
            Some(v) if v < 0 => -1,
            Some(_) => 0,
            None => {
                // For large integers, check if it's ofNat or negSucc
                if Self::isNonNeg(obj) {
                    1
                } else {
                    -1
                }
            }
        }
    }

    /// Get the absolute value as a natural number.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.natAbs` in Lean4.
    #[allow(non_snake_case)]
    pub fn natAbs<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanNat>> {
        let lean = obj.lean_token();
        match Self::to_i64(obj) {
            Some(v) => {
                let abs_val = v.unsigned_abs() as usize;
                LeanNat::from_usize(lean, abs_val)
            }
            None => {
                // For large integers, we would need to implement this with Lean FFI
                // For now, this is a limitation
                unsafe {
                    if Self::isNonNeg(obj) {
                        // It's ofNat, so we can get the nat directly
                        let ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
                        ffi::lean_inc(ptr);
                        Ok(LeanBound::from_owned_ptr(lean, ptr))
                    } else {
                        // It's negSucc n, need to compute n + 1
                        let n = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
                        ffi::lean_inc(n);
                        let one = ffi::inline::lean_box(1);
                        let result = ffi::inline::lean_nat_add(n, one);
                        Ok(LeanBound::from_owned_ptr(lean, result))
                    }
                }
            }
        }
    }

    /// Convert to a natural number if non-negative.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.toNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn toNat<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanNat>> {
        let lean = obj.lean_token();
        if Self::isNonNeg(obj) {
            Self::natAbs(obj)
        } else {
            LeanNat::from_usize(lean, 0)
        }
    }

    /// Try to convert to a natural number, returning None if negative.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Int.toNat?` in Lean4.
    #[allow(non_snake_case)]
    pub fn toNatOption<'l>(
        obj: &LeanBound<'l, Self>,
    ) -> Option<LeanResult<LeanBound<'l, LeanNat>>> {
        if Self::isNonNeg(obj) {
            Some(Self::natAbs(obj))
        } else {
            None
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match LeanInt::to_i64(self) {
            Some(v) => write!(f, "LeanInt({})", v),
            None => write!(f, "LeanInt(<large>)"),
        }
    }
}
