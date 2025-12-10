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
        unsafe {
            let val = ffi::float::lean_float_of_bits(bits);
            Self::from_f64(lean, val)
        }
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
        unsafe { ffi::float::lean_float_to_bits(Self::to_f64(obj)) }
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

    // ========================================================================
    // Creation from integers
    // ========================================================================

    /// Create a Float from an Int (LeanInt).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.ofInt` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofInt<'l>(
        n: &LeanBound<'l, crate::types::LeanInt>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // Convert LeanInt to f64 via i64 approximation for now
        // In a full implementation, this would handle arbitrary precision
        let val = crate::types::LeanInt::to_i64(n).unwrap_or(0);
        Self::from_f64(lean, val as f64)
    }

    /// Create a Float from a Nat (LeanNat).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.ofNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofNat<'l>(
        n: &LeanBound<'l, crate::types::LeanNat>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // Convert LeanNat to f64 via usize approximation for now
        // In a full implementation, this would handle arbitrary precision
        let val = crate::types::LeanNat::to_usize(n).unwrap_or(0);
        Self::from_f64(lean, val as f64)
    }

    /// Convert float to string.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toString` in Lean4.
    #[allow(non_snake_case)]
    pub fn toString<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanString>> {
        unsafe {
            let ptr = ffi::float::lean_float_to_string(Self::to_f64(obj));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Scale a float by a power of 2 (multiply by 2^n).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.scaleB` in Lean4.
    #[allow(non_snake_case)]
    pub fn scaleB<'l>(
        obj: &LeanBound<'l, Self>,
        n: &LeanBound<'l, crate::types::LeanInt>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float_scaleb(Self::to_f64(obj), n.as_ptr());
            Self::from_f64(lean, result)
        }
    }

    /// Extract mantissa and exponent (frexp).
    ///
    /// Returns a pair `(mantissa, exponent)` where the float is equal to
    /// `mantissa * 2^exponent`, with mantissa in the range [0.5, 1.0).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.frExp` in Lean4.
    #[allow(non_snake_case)]
    pub fn frExp<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanProd>> {
        unsafe {
            let ptr = ffi::float::lean_float_frexp(Self::to_f64(obj));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
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
        unsafe {
            let result = ffi::inline::lean_float_add(Self::to_f64(a), Self::to_f64(b));
            Self::from_f64(lean, result)
        }
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
        unsafe {
            let result = ffi::inline::lean_float_sub(Self::to_f64(a), Self::to_f64(b));
            Self::from_f64(lean, result)
        }
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
        unsafe {
            let result = ffi::inline::lean_float_mul(Self::to_f64(a), Self::to_f64(b));
            Self::from_f64(lean, result)
        }
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
        unsafe {
            let result = ffi::inline::lean_float_div(Self::to_f64(a), Self::to_f64(b));
            Self::from_f64(lean, result)
        }
    }

    /// Negate a float.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.neg` or `-x` in Lean4.
    pub fn neg<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::inline::lean_float_negate(Self::to_f64(&obj));
            Self::from_f64(lean, result)
        }
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
        unsafe { ffi::inline::lean_float_beq(Self::to_f64(a), Self::to_f64(b)) != 0 }
    }

    /// Check if first float is less than second.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_float_decLt(Self::to_f64(a), Self::to_f64(b)) != 0 }
    }

    /// Check if first float is less than or equal to second.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_float_decLe(Self::to_f64(a), Self::to_f64(b)) != 0 }
    }

    // ========================================================================
    // Integer conversion methods
    // ========================================================================

    /// Convert Float to UInt8 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toUInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt8<'l>(obj: &LeanBound<'l, Self>) -> u8 {
        unsafe { ffi::inline::lean_float_to_uint8(Self::to_f64(obj)) }
    }

    /// Convert Float to UInt16 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toUInt16` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt16<'l>(obj: &LeanBound<'l, Self>) -> u16 {
        unsafe { ffi::inline::lean_float_to_uint16(Self::to_f64(obj)) }
    }

    /// Convert Float to UInt32 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toUInt32` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt32<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { ffi::inline::lean_float_to_uint32(Self::to_f64(obj)) }
    }

    /// Convert Float to UInt64 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toUInt64` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt64<'l>(obj: &LeanBound<'l, Self>) -> u64 {
        unsafe { ffi::inline::lean_float_to_uint64(Self::to_f64(obj)) }
    }

    /// Convert Float to USize (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toUSize` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUSize<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::inline::lean_float_to_usize(Self::to_f64(obj)) }
    }

    /// Convert Float to Int8 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt8<'l>(obj: &LeanBound<'l, Self>) -> i8 {
        unsafe { ffi::inline::lean_float_to_int8(Self::to_f64(obj)) }
    }

    /// Convert Float to Int16 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toInt16` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt16<'l>(obj: &LeanBound<'l, Self>) -> i16 {
        unsafe { ffi::inline::lean_float_to_int16(Self::to_f64(obj)) }
    }

    /// Convert Float to Int32 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toInt32` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt32<'l>(obj: &LeanBound<'l, Self>) -> i32 {
        unsafe { ffi::inline::lean_float_to_int32(Self::to_f64(obj)) }
    }

    /// Convert Float to Int64 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toInt64` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt64<'l>(obj: &LeanBound<'l, Self>) -> i64 {
        unsafe { ffi::inline::lean_float_to_int64(Self::to_f64(obj)) }
    }

    /// Convert Float to ISize (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.toISize` in Lean4.
    #[allow(non_snake_case)]
    pub fn toISize<'l>(obj: &LeanBound<'l, Self>) -> isize {
        unsafe { ffi::inline::lean_float_to_isize(Self::to_f64(obj)) }
    }

    // ========================================================================
    // Decidable comparison methods
    // ========================================================================

    /// Decidable less than comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.decLt` in Lean4.
    #[allow(non_snake_case)]
    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_float_decLt(Self::to_f64(a), Self::to_f64(b)) != 0 }
    }

    /// Decidable less than or equal comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float.decLe` in Lean4.
    #[allow(non_snake_case)]
    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::inline::lean_float_decLe(Self::to_f64(a), Self::to_f64(b)) != 0 }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanFloat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanFloat({})", LeanFloat::to_f64(self))
    }
}
