//! Lean natural number type wrapper.

use crate::ffi;
use crate::marker::Lean;
use crate::instance::LeanBound;
use crate::err::{LeanResult, LeanError};

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
            let ptr = ffi::nat::lean_usize_to_nat(n);
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
            if ffi::nat::lean_nat_is_small(obj.as_ptr()) {
                Ok(ffi::nat::lean_nat_to_usize(obj.as_ptr()))
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
        unsafe { ffi::nat::lean_nat_is_small(obj.as_ptr()) }
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
            let ptr = ffi::nat::lean_nat_add(a.into_ptr(), b.into_ptr());
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
            let ptr = ffi::nat::lean_nat_sub(a.into_ptr(), b.into_ptr());
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
            let ptr = ffi::nat::lean_nat_mul(a.into_ptr(), b.into_ptr());
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
            let ptr = ffi::nat::lean_nat_div(a.into_ptr(), b.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Modulo operation.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 47)?;
    /// let b = LeanNat::from_usize(lean, 5)?;
    /// let remainder = LeanNat::modulo(a, b)?;
    /// assert_eq!(LeanNat::to_usize(&remainder)?, 2);
    /// ```
    pub fn modulo<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::nat::lean_nat_mod(a.into_ptr(), b.into_ptr());
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

    /// Compare two natural numbers for equality.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 42)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::eq(&a, &b));
    /// ```
    pub fn eq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::nat::lean_nat_dec_eq(a.as_ptr(), b.as_ptr()) }
    }

    /// Compare two natural numbers for less-than.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let a = LeanNat::from_usize(lean, 10)?;
    /// let b = LeanNat::from_usize(lean, 42)?;
    /// assert!(LeanNat::lt(&a, &b));
    /// ```
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::nat::lean_nat_dec_lt(a.as_ptr(), b.as_ptr()) }
    }

    /// Compare two natural numbers for less-than-or-equal.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::nat::lean_nat_dec_le(a.as_ptr(), b.as_ptr()) }
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
