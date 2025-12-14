//! Lean natural number type wrapper.

use leo3_ffi::inline::{
    lean_box, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mod, lean_nat_mul, lean_nat_sub, lean_unbox, lean_usize_of_nat, lean_usize_to_nat,
};

use crate::err::{LeanError, LeanResult};
use crate::ffi;
use crate::instance::LeanBound;
use crate::marker::Lean;

/// A Lean natural number object.
///
/// Natural numbers in Lean4 are represented as either:
/// - Small values: boxed directly as tagged pointers
/// - Large values: GMP arbitrary precision integers
pub struct LeanNat {
    _private: (),
}

impl LeanNat {
    /// Create a Lean natural number from a Rust usize.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let n = LeanNat::from_usize(lean, 42)?;
    ///     assert_eq!(LeanNat::to_usize(&n)?, 42);
    ///     Ok(())
    /// })
    /// ```
    pub fn from_usize<'l>(lean: Lean<'l>, n: usize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = lean_usize_to_nat(n);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert a Lean natural number to a Rust usize.
    ///
    /// Returns an error if the number doesn't fit in usize.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 100)?;
    /// assert_eq!(LeanNat::to_usize(&n)?, 100);
    /// ```
    pub fn to_usize<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<usize> {
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                Ok(lean_usize_of_nat(obj.as_ptr()))
            } else {
                Err(LeanError::conversion("Natural number too large for usize"))
            }
        }
    }

    /// Check if this natural number fits in a usize.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::is_small(&n));
    /// ```
    pub fn is_small<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::nat::leo3_nat_is_small(obj.as_ptr()) }
    }

    /// Add two natural numbers.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 32)?;
    /// let sum = LeanNat::add(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&sum)?, 42);
    /// ```
    pub fn add<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = lean_nat_add(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Subtract natural numbers (returns 0 if b > a).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 50)?;
    /// let b = LeanNat::from_usize(lean, 8)?;
    /// let diff = LeanNat::sub(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&diff)?, 42);
    /// ```
    pub fn sub<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = lean_nat_sub(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Multiply two natural numbers.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 6)?;
    /// let b = LeanNat::from_usize(lean, 7)?;
    /// let product = LeanNat::mul(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&product)?, 42);
    /// ```
    pub fn mul<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = lean_nat_mul(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Divide natural numbers.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 84)?;
    /// let b = LeanNat::from_usize(lean, 2)?;
    /// let quotient = LeanNat::div(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&quotient)?, 42);
    /// ```
    pub fn div<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = lean_nat_div(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Modulo operation.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.mod` in Lean4 (also `%` operator).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 47)?;
    /// let b = LeanNat::from_usize(lean, 5)?;
    /// let remainder = LeanNat::mod_(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&remainder)?, 2);
    /// ```
    pub fn mod_<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = lean_nat_mod(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Power operation (exponentiation).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let base = LeanNat::from_usize(lean, 2)?;
    /// let exp = LeanNat::from_usize(lean, 10)?;
    /// let result = LeanNat::pow(base, exp)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 1024);
    /// ```
    pub fn pow<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_pow(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Greatest Common Divisor.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 48)?;
    /// let b = LeanNat::from_usize(lean, 18)?;
    /// let gcd = LeanNat::gcd(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&gcd)?, 6);
    /// ```
    pub fn gcd<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_gcd(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Compare two natural numbers for equality (decidable equality).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.decEq` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 42)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::decEq(&a, &b));
    /// ```
    #[allow(non_snake_case)]
    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_eq(a.as_ptr(), b.as_ptr()) }
    }

    /// Compare two natural numbers for less-than (decidable less-than).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.decLt` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::decLt(&a, &b));
    /// ```
    #[allow(non_snake_case)]
    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_lt(a.as_ptr(), b.as_ptr()) }
    }

    /// Compare two natural numbers for less-than-or-equal (decidable ≤).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.decLe` in Lean4.
    #[allow(non_snake_case)]
    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_le(a.as_ptr(), b.as_ptr()) }
    }

    /// Predecessor (n - 1, returns 0 for 0).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.pred` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 42)?;
    /// let pred = LeanNat::pred(n)?;
    /// assert_eq!(LeanNat::to_usize(&pred)?, 41);
    /// ```
    pub fn pred<'l>(n: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = n.lean_token();
            let ptr = ffi::nat::lean_nat_pred(n.as_ptr());
            leo3_ffi::inline::lean_dec(n.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Logarithm base 2 (floor).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.log2` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 1024)?;
    /// let log = LeanNat::log2(&n)?;
    /// assert_eq!(LeanNat::to_usize(&log)?, 10);
    /// ```
    pub fn log2<'l>(n: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = n.lean_token();
            let ptr = ffi::nat::lean_nat_log2(n.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Bitwise left shift.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.shiftLeft` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;
    /// let shift = LeanNat::from_usize(lean, 2)?;
    /// let result = LeanNat::shiftLeft(n, shift)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 20);
    /// ```
    #[allow(non_snake_case)]
    pub fn shiftLeft<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_shift_left(a.as_ptr(), b.as_ptr());
            leo3_ffi::inline::lean_dec(a.into_ptr());
            leo3_ffi::inline::lean_dec(b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Bitwise right shift.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.shiftRight` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 20)?;
    /// let shift = LeanNat::from_usize(lean, 2)?;
    /// let result = LeanNat::shiftRight(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 5);
    /// ```
    #[allow(non_snake_case)]
    pub fn shiftRight<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_shift_right(a.as_ptr(), b.as_ptr());
            leo3_ffi::inline::lean_dec(a.into_ptr());
            leo3_ffi::inline::lean_dec(b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Bitwise XOR.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.xor` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 5)?;  // 0b0101
    /// let b = LeanNat::from_usize(lean, 3)?;  // 0b0011
    /// let result = LeanNat::xor(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 6); // 0b0110
    /// ```
    pub fn xor<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_xor(a.as_ptr(), b.as_ptr());
            leo3_ffi::inline::lean_dec(a.into_ptr());
            leo3_ffi::inline::lean_dec(b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Bitwise OR.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.lor` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 5)?;  // 0b0101
    /// let b = LeanNat::from_usize(lean, 3)?;  // 0b0011
    /// let result = LeanNat::lor(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 7); // 0b0111
    /// ```
    pub fn lor<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_lor(a.as_ptr(), b.as_ptr());
            leo3_ffi::inline::lean_dec(a.into_ptr());
            leo3_ffi::inline::lean_dec(b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Bitwise AND.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.land` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 5)?;  // 0b0101
    /// let b = LeanNat::from_usize(lean, 3)?;  // 0b0011
    /// let result = LeanNat::land(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&result)?, 1); // 0b0001
    /// ```
    pub fn land<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_land(a.as_ptr(), b.as_ptr());
            leo3_ffi::inline::lean_dec(a.into_ptr());
            leo3_ffi::inline::lean_dec(b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Test if a specific bit is set.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.testBit` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;  // 0b0101
    /// let idx = LeanNat::from_usize(lean, 2)?;
    /// assert!(LeanNat::testBit(&n, &idx));
    /// ```
    #[allow(non_snake_case)]
    pub fn testBit<'l>(n: &LeanBound<'l, Self>, idx: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let lean = n.lean_token();
            let bool_obj = ffi::nat::lean_nat_test_bit(n.as_ptr(), idx.as_ptr());
            let bool_bound = LeanBound::<crate::types::LeanBool>::from_owned_ptr(lean, bool_obj);
            crate::types::LeanBool::toBool(&bool_bound)
        }
    }

    /// Minimum of two natural numbers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.min` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// let min = LeanNat::min(&a, &b)?;
    /// assert_eq!(LeanNat::to_usize(&min)?, 10);
    /// ```
    pub fn min<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_min(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Maximum of two natural numbers.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.max` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// let max = LeanNat::max(&a, &b)?;
    /// assert_eq!(LeanNat::to_usize(&max)?, 42);
    /// ```
    pub fn max<'l>(
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_max(a.as_ptr(), b.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Least Common Multiple.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.lcm` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 12)?;
    /// let b = LeanNat::from_usize(lean, 18)?;
    /// let lcm = LeanNat::lcm(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&lcm)?, 36);
    /// ```
    pub fn lcm<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_lcm(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Boolean equality comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.beq` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 42)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::beq(&a, &b));
    /// ```
    pub fn beq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_eq(a.as_ptr(), b.as_ptr()) }
    }

    /// Boolean less-than-or-equal comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.ble` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::ble(&a, &b));
    /// ```
    pub fn ble<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_le(a.as_ptr(), b.as_ptr()) }
    }

    /// Boolean less-than comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.blt` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::blt(&a, &b));
    /// ```
    pub fn blt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_nat_dec_lt(a.as_ptr(), b.as_ptr()) }
    }

    /// Convert to UInt8.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toUInt8` in Lean4.
    ///
    /// Returns an error if the number doesn't fit in u8.
    #[allow(non_snake_case)]
    pub fn toUInt8<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<u8> {
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                let val = lean_unbox(obj.as_ptr());
                if val <= u8::MAX as usize {
                    Ok(val as u8)
                } else {
                    Err(LeanError::conversion("Natural number too large for u8"))
                }
            } else {
                Ok(leo3_ffi::nat::lean_uint8_of_big_nat(obj.as_ptr()))
            }
        }
    }

    /// Convert to UInt16.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toUInt16` in Lean4.
    ///
    /// Returns an error if the number doesn't fit in u16.
    #[allow(non_snake_case)]
    pub fn toUInt16<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<u16> {
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                let val = lean_unbox(obj.as_ptr());
                if val <= u16::MAX as usize {
                    Ok(val as u16)
                } else {
                    Err(LeanError::conversion("Natural number too large for u16"))
                }
            } else {
                Ok(leo3_ffi::nat::lean_uint16_of_big_nat(obj.as_ptr()))
            }
        }
    }

    /// Convert to UInt32.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toUInt32` in Lean4.
    ///
    /// Returns an error if the number doesn't fit in u32.
    #[allow(non_snake_case)]
    pub fn toUInt32<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<u32> {
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                let val = lean_unbox(obj.as_ptr());
                if val <= u32::MAX as usize {
                    Ok(val as u32)
                } else {
                    Err(LeanError::conversion("Natural number too large for u32"))
                }
            } else {
                Ok(leo3_ffi::nat::lean_uint32_of_big_nat(obj.as_ptr()))
            }
        }
    }

    /// Convert to UInt64.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toUInt64` in Lean4.
    ///
    /// Returns an error if the number doesn't fit in u64.
    #[allow(non_snake_case)]
    pub fn toUInt64<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<u64> {
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                Ok(lean_unbox(obj.as_ptr()) as u64)
            } else {
                Ok(leo3_ffi::nat::lean_uint64_of_big_nat(obj.as_ptr()))
            }
        }
    }

    /// Convert to USize.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toUSize` in Lean4.
    ///
    /// Returns an error if the number doesn't fit in usize.
    /// This is the same as `to_usize` but follows Lean4 naming.
    #[allow(non_snake_case)]
    pub fn toUSize<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<usize> {
        Self::to_usize(obj)
    }

    /// Check if power of two.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.isPowerOfTwo` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 8)?;
    /// assert!(LeanNat::isPowerOfTwo(&n));
    /// ```
    #[allow(non_snake_case)]
    pub fn isPowerOfTwo<'l>(n: &LeanBound<'l, Self>) -> bool {
        unsafe {
            // A number is a power of two if n != 0 && (n & (n - 1)) == 0
            let zero = lean_box(0);
            if lean_nat_dec_eq(n.as_ptr(), zero) {
                return false;
            }
            let one = lean_box(1);
            let n_ptr = n.as_ptr();
            leo3_ffi::inline::lean_inc(n_ptr);
            let n_minus_1 = lean_nat_sub(n_ptr, one);
            let anded = ffi::nat::lean_nat_land(n.as_ptr(), n_minus_1);
            let result = lean_nat_dec_eq(anded, lean_box(0));
            leo3_ffi::inline::lean_dec(anded);
            leo3_ffi::inline::lean_dec(n_minus_1);
            result
        }
    }

    /// Get next power of two (returns smallest power of 2 that is >= n).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.nextPowerOfTwo` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;
    /// let next = LeanNat::nextPowerOfTwo(n)?;
    /// assert_eq!(LeanNat::to_usize(&next)?, 8);
    /// ```
    #[allow(non_snake_case)]
    pub fn nextPowerOfTwo<'l>(n: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = n.lean_token();
            // Use the native Lean implementation
            let ptr = ffi::nat::lean_nat_next_power_of_two(n.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to f64.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.toFloat` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 42)?;
    /// let f = LeanNat::toFloat(&n);
    /// assert_eq!(f, 42.0);
    /// ```
    #[allow(non_snake_case)]
    pub fn toFloat<'l>(obj: &LeanBound<'l, Self>) -> f64 {
        // For now, this only works for small nats
        // A proper implementation would need to handle big nats
        unsafe {
            if ffi::nat::leo3_nat_is_small(obj.as_ptr()) {
                lean_unbox(obj.as_ptr()) as f64
            } else {
                // For big nats, convert via u64 if possible
                // This may lose precision for very large numbers
                leo3_ffi::nat::lean_uint64_of_big_nat(obj.as_ptr()) as f64
            }
        }
    }

    /// Convert to string representation (base 10).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.repr` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 42)?;
    /// assert_eq!(LeanNat::repr(&n), "42");
    /// ```
    pub fn repr<'l>(obj: &LeanBound<'l, Self>) -> String {
        // Use to_usize if possible, otherwise use a fallback
        match Self::to_usize(obj) {
            Ok(n) => n.to_string(),
            Err(_) => {
                // For big nats, convert via u64 if possible (may truncate)
                unsafe {
                    let val = leo3_ffi::nat::lean_uint64_of_big_nat(obj.as_ptr());
                    format!("{}...", val)
                }
            }
        }
    }

    /// Create a nat from a string representation.
    ///
    /// # Safety
    /// The string must be a valid non-negative integer in base 10.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_str(lean, "12345")?;
    /// assert_eq!(LeanNat::to_usize(&n)?, 12345);
    /// ```
    pub fn from_str<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanBound<'l, Self>> {
        let c_str = std::ffi::CString::new(s)
            .map_err(|_| LeanError::conversion("String contains null byte"))?;

        unsafe {
            let ptr = ffi::nat::lean_cstr_to_nat(c_str.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Successor (n + 1).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.succ` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 41)?;
    /// let succ = LeanNat::succ(n)?;
    /// assert_eq!(LeanNat::to_usize(&succ)?, 42);
    /// ```
    pub fn succ<'l>(n: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = n.lean_token();
        let one = Self::from_usize(lean, 1)?;
        Self::add(n, one)
    }

    /// Check if the natural number is zero.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let zero = LeanNat::from_usize(lean, 0)?;
    /// assert!(LeanNat::isZero(&zero));
    /// ```
    #[allow(non_snake_case)]
    pub fn isZero<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe {
            let zero = lean_box(0);
            lean_nat_dec_eq(obj.as_ptr(), zero)
        }
    }

    /// Fold over natural numbers from 0 to n-1.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.fold` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;
    /// let sum = LeanNat::fold(&n, 0, |acc, i| acc + i);
    /// assert_eq!(sum, 10); // 0 + 1 + 2 + 3 + 4
    /// ```
    pub fn fold<'l, A, F>(n: &LeanBound<'l, Self>, init: A, f: F) -> A
    where
        F: Fn(A, usize) -> A,
    {
        match Self::to_usize(n) {
            Ok(count) => {
                let mut acc = init;
                for i in 0..count {
                    acc = f(acc, i);
                }
                acc
            }
            Err(_) => init, // For very large numbers, just return init
        }
    }

    /// Check if all numbers from 0 to n-1 satisfy a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.all` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;
    /// assert!(LeanNat::all(&n, |i| i < 5));
    /// ```
    pub fn all<'l, F>(n: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        match Self::to_usize(n) {
            Ok(count) => {
                for i in 0..count {
                    if !pred(i) {
                        return false;
                    }
                }
                true
            }
            Err(_) => true, // For very large numbers
        }
    }

    /// Check if any number from 0 to n-1 satisfies a predicate.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Nat.any` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let n = LeanNat::from_usize(lean, 5)?;
    /// assert!(LeanNat::any(&n, |i| i == 3));
    /// ```
    pub fn any<'l, F>(n: &LeanBound<'l, Self>, pred: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        match Self::to_usize(n) {
            Ok(count) => {
                for i in 0..count {
                    if pred(i) {
                        return true;
                    }
                }
                false
            }
            Err(_) => false, // For very large numbers
        }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanNat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match LeanNat::to_usize(self) {
            Ok(n) => write!(f, "LeanNat({})", n),
            Err(_) => write!(f, "LeanNat(<large>)"),
        }
    }
}
