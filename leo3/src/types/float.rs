//! Lean floating-point number type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::inline::{lean_box_float, lean_unbox_float};
use crate::instance::LeanBound;
use crate::marker::Lean;

/// A Lean 64-bit floating-point number.
///
/// Float in Lean4 corresponds to IEEE 754 *binary64* format (f64 in Rust, double in C).
///
/// Floating-point numbers include:
/// - Normal numbers
/// - Subnormal numbers
/// - NaN (Not a Number)
/// - +Inf and -Inf
/// - +0.0 and -0.0
///
/// # Lean4 Reference
/// ```lean
/// structure Float where
///   val : floatSpec.float
/// ```
pub struct LeanFloat {
    _private: (),
}

impl LeanFloat {
    /// Create a Lean float from an f64.
    ///
    /// # Lean4 Reference
    /// Corresponds to creating a Float value in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let f = LeanFloat::from_f64(lean, 3.14159)?;
    ///     assert_eq!(LeanFloat::to_f64(&f), 3.14159);
    ///     Ok(())
    /// })
    /// ```
    pub fn from_f64<'l>(lean: Lean<'l>, value: f64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = lean_box_float(value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Lean float from bits (IEEE 754 representation).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.ofBits` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofBits<'l>(lean: Lean<'l>, bits: u64) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, f64::from_bits(bits))
    }

    /// Convert a Lean float to an f64.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let f = LeanFloat::from_f64(lean, 2.5)?;
    /// assert_eq!(LeanFloat::to_f64(&f), 2.5);
    /// ```
    pub fn to_f64<'l>(obj: &LeanBound<'l, Self>) -> f64 {
        unsafe { lean_unbox_float(obj.as_ptr()) }
    }

    /// Convert to bits (IEEE 754 representation).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toBits` in Lean4.
    #[allow(non_snake_case)]
    pub fn toBits<'l>(obj: &LeanBound<'l, Self>) -> u64 {
        Self::to_f64(obj).to_bits()
    }

    /// Create a zero float.
    pub fn zero<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, 0.0)
    }

    /// Create a one float.
    pub fn one<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, 1.0)
    }

    /// Create positive infinity.
    pub fn infinity<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, f64::INFINITY)
    }

    /// Create negative infinity.
    pub fn neg_infinity<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, f64::NEG_INFINITY)
    }

    /// Create NaN (Not a Number).
    pub fn nan<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f64(lean, f64::NAN)
    }

    /// Check if the float is NaN.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.isNaN` in Lean4.
    #[allow(non_snake_case)]
    pub fn isNaN<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float_isnan(Self::to_f64(obj)) != 0 }
    }

    /// Check if the float is finite (not infinite and not NaN).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.isFinite` in Lean4.
    #[allow(non_snake_case)]
    pub fn isFinite<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float_isfinite(Self::to_f64(obj)) != 0 }
    }

    /// Convert to LeanFloat32 (32-bit float).
    #[allow(non_snake_case)]
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let result = ffi::inline::lean_float_to_float32(Self::to_f64(obj));
            crate::types::LeanFloat32::from_f32(lean, result)
        }
    }

    /// Check if the float is infinite.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.isInf` in Lean4.
    #[allow(non_snake_case)]
    pub fn isInf<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float_isinf(Self::to_f64(obj)) != 0 }
    }

    /// Add two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.add` or `+` operator in Lean4.
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(a) + Self::to_f64(b);
        Self::from_f64(lean, result)
    }

    /// Subtract two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.sub` or `-` operator in Lean4.
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(a) - Self::to_f64(b);
        Self::from_f64(lean, result)
    }

    /// Multiply two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.mul` or `*` operator in Lean4.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(a) * Self::to_f64(b);
        Self::from_f64(lean, result)
    }

    /// Divide two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.div` or `/` operator in Lean4.
    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(a) / Self::to_f64(b);
        Self::from_f64(lean, result)
    }

    /// Negate a float.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.neg` or `-x` in Lean4.
    pub fn neg<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = -Self::to_f64(&obj);
        Self::from_f64(lean, result)
    }

    /// Absolute value.
    pub fn abs<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(&obj).abs();
        Self::from_f64(lean, result)
    }

    /// Square root.
    pub fn sqrt<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(&obj).sqrt();
        Self::from_f64(lean, result)
    }

    /// Power function.
    pub fn pow<'l>(
        lean: Lean<'l>,
        base: &LeanBound<'l, Self>,
        exp: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(base).powf(Self::to_f64(exp));
        Self::from_f64(lean, result)
    }

    /// Floor function.
    pub fn floor<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(&obj).floor();
        Self::from_f64(lean, result)
    }

    /// Ceiling function.
    pub fn ceil<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(&obj).ceil();
        Self::from_f64(lean, result)
    }

    /// Round to nearest integer.
    pub fn round<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f64(&obj).round();
        Self::from_f64(lean, result)
    }

    /// Check equality of two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.beq` or `==` in Lean4.
    ///
    /// Note: This uses bit-wise equality, so NaN != NaN.
    pub fn beq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f64(a) == Self::to_f64(b)
    }

    /// Check if first float is less than second.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f64(a) < Self::to_f64(b)
    }

    /// Check if first float is less than or equal to second.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f64(a) <= Self::to_f64(b)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanFloat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanFloat({})", LeanFloat::to_f64(self))
    }
}
