//! Lean 32-bit floating-point number type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::inline::{lean_box_float32, lean_unbox_float32};
use crate::instance::LeanBound;
use crate::marker::Lean;

/// A Lean 32-bit floating-point number.
///
/// Float32 in Lean4 corresponds to IEEE 754 *binary32* format (f32 in Rust, float in C).
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
/// structure Float32 where
///   ofUInt32 :: toUInt32 : UInt32
/// ```
pub struct LeanFloat32 {
    _private: (),
}

impl LeanFloat32 {
    /// Create a Lean Float32 from an f32.
    ///
    /// # Lean4 Reference
    /// Corresponds to creating a Float32 value in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let f = LeanFloat32::from_f32(lean, 3.14159)?;
    ///     assert_eq!(LeanFloat32::to_f32(&f), 3.14159);
    ///     Ok(())
    /// })
    /// ```
    pub fn from_f32<'l>(lean: Lean<'l>, value: f32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = lean_box_float32(value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
    /// Convert a Lean Float32 to an f32.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let f = LeanFloat32::from_f32(lean, 2.5)?;
    /// assert_eq!(LeanFloat32::to_f32(&f), 2.5);
    /// ```
    pub fn to_f32<'l>(obj: &LeanBound<'l, Self>) -> f32 {
        unsafe { lean_unbox_float32(obj.as_ptr()) }
    }

    /// Create a Lean Float32 from bits (IEEE 754 representation).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.ofBits` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofBits<'l>(lean: Lean<'l>, bits: u32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::float::lean_float32_of_bits(bits);
            Self::from_f32(lean, val)
        }
    }

    /// Convert to bits (IEEE 754 representation).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toBits` in Lean4.
    #[allow(non_snake_case)]
    pub fn toBits<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { ffi::float::lean_float32_to_bits(Self::to_f32(obj)) }
    }

    /// Create a zero float.
    pub fn zero<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f32(lean, 0.0)
    }

    /// Create a one float.
    pub fn one<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f32(lean, 1.0)
    }

    /// Create positive infinity.
    pub fn infinity<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f32(lean, f32::INFINITY)
    }

    /// Create negative infinity.
    pub fn neg_infinity<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f32(lean, f32::NEG_INFINITY)
    }

    /// Create NaN (Not a Number).
    pub fn nan<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        Self::from_f32(lean, f32::NAN)
    }

    /// Check if the float is NaN.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.isNaN` in Lean4.
    #[allow(non_snake_case)]
    pub fn isNaN<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float32_isnan(Self::to_f32(obj)) != 0 }
    }

    /// Check if the float is finite (not infinite and not NaN).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.isFinite` in Lean4.
    #[allow(non_snake_case)]
    pub fn isFinite<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float32_isfinite(Self::to_f32(obj)) != 0 }
    }

    /// Check if the float is infinite.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.isInf` in Lean4.
    #[allow(non_snake_case)]
    pub fn isInf<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float32_isinf(Self::to_f32(obj)) != 0 }
    }

    /// Add two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.add` or `+` operator in Lean4.
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_add(Self::to_f32(a), Self::to_f32(b));
            Self::from_f32(lean, result)
        }
    }

    /// Subtract two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.sub` or `-` operator in Lean4.
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_sub(Self::to_f32(a), Self::to_f32(b));
            Self::from_f32(lean, result)
        }
    }

    /// Multiply two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.mul` or `*` operator in Lean4.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_mul(Self::to_f32(a), Self::to_f32(b));
            Self::from_f32(lean, result)
        }
    }

    /// Divide two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.div` or `/` operator in Lean4.
    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_div(Self::to_f32(a), Self::to_f32(b));
            Self::from_f32(lean, result)
        }
    }

    /// Negate a float.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.neg` or `-x` in Lean4.
    pub fn neg<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_negate(Self::to_f32(&obj));
            Self::from_f32(lean, result)
        }
    }

    /// Absolute value.
    pub fn abs<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(&obj).abs();
        Self::from_f32(lean, result)
    }

    /// Square root.
    pub fn sqrt<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(&obj).sqrt();
        Self::from_f32(lean, result)
    }

    /// Power function.
    pub fn pow<'l>(
        lean: Lean<'l>,
        base: &LeanBound<'l, Self>,
        exp: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(base).powf(Self::to_f32(exp));
        Self::from_f32(lean, result)
    }

    /// Floor function.
    pub fn floor<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(&obj).floor();
        Self::from_f32(lean, result)
    }

    /// Ceiling function.
    pub fn ceil<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(&obj).ceil();
        Self::from_f32(lean, result)
    }

    /// Round to nearest integer.
    pub fn round<'l>(lean: Lean<'l>, obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let result = Self::to_f32(&obj).round();
        Self::from_f32(lean, result)
    }

    /// Check equality of two floats.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.beq` or `==` in Lean4.
    ///
    /// Note: This uses bit-wise equality, so NaN != NaN.
    pub fn beq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f32(a) == Self::to_f32(b)
    }

    /// Check if first float is less than second.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f32(a) < Self::to_f32(b)
    }

    /// Check if first float is less than or equal to second.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::to_f32(a) <= Self::to_f32(b)
    }

    /// Convert to LeanFloat (64-bit float).
    #[allow(non_snake_case)]
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let result = ffi::inline::lean_float32_to_float(Self::to_f32(obj));
            crate::types::LeanFloat::from_f64(lean, result)
        }
    }

    /// Convert float32 to string.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toString` in Lean4.
    #[allow(non_snake_case)]
    pub fn toString<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanString>> {
        unsafe {
            let ptr = ffi::float::lean_float32_to_string(Self::to_f32(obj));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Scale a float32 by a power of 2 (multiply by 2^n).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.scaleB` in Lean4.
    #[allow(non_snake_case)]
    pub fn scaleB<'l>(
        obj: &LeanBound<'l, Self>,
        n: &LeanBound<'l, crate::types::LeanInt>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = ffi::float::lean_float32_scaleb(Self::to_f32(obj), n.as_ptr());
            Self::from_f32(lean, result)
        }
    }

    /// Extract mantissa and exponent (frexp).
    ///
    /// Returns a pair `(mantissa, exponent)` where the float is equal to
    /// `mantissa * 2^exponent`, with mantissa in the range [0.5, 1.0).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.frExp` in Lean4.
    #[allow(non_snake_case)]
    pub fn frExp<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanProd>> {
        unsafe {
            let ptr = ffi::float::lean_float32_frexp(Self::to_f32(obj));
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // ========================================================================
    // Conversion to unsigned integers
    // ========================================================================

    /// Convert Float32 to UInt8 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toUInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt8<'l>(obj: &LeanBound<'l, Self>) -> u8 {
        unsafe { ffi::inline::lean_float32_to_uint8(Self::to_f32(obj)) }
    }

    /// Convert Float32 to UInt16 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toUInt16` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt16<'l>(obj: &LeanBound<'l, Self>) -> u16 {
        unsafe { ffi::inline::lean_float32_to_uint16(Self::to_f32(obj)) }
    }

    /// Convert Float32 to UInt32 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toUInt32` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt32<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { ffi::inline::lean_float32_to_uint32(Self::to_f32(obj)) }
    }

    /// Convert Float32 to UInt64 (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toUInt64` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt64<'l>(obj: &LeanBound<'l, Self>) -> u64 {
        unsafe { ffi::inline::lean_float32_to_uint64(Self::to_f32(obj)) }
    }

    /// Convert Float32 to USize (with bounds checking).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toUSize` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUSize<'l>(obj: &LeanBound<'l, Self>) -> usize {
        unsafe { ffi::inline::lean_float32_to_usize(Self::to_f32(obj)) }
    }

    // ========================================================================
    // Conversion to signed integers
    // ========================================================================

    /// Convert Float32 to Int8 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt8<'l>(obj: &LeanBound<'l, Self>) -> i8 {
        unsafe { ffi::inline::lean_float32_to_int8(Self::to_f32(obj)) }
    }

    /// Convert Float32 to Int16 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toInt16` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt16<'l>(obj: &LeanBound<'l, Self>) -> i16 {
        unsafe { ffi::inline::lean_float32_to_int16(Self::to_f32(obj)) }
    }

    /// Convert Float32 to Int32 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toInt32` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt32<'l>(obj: &LeanBound<'l, Self>) -> i32 {
        unsafe { ffi::inline::lean_float32_to_int32(Self::to_f32(obj)) }
    }

    /// Convert Float32 to Int64 (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toInt64` in Lean4.
    #[allow(non_snake_case)]
    pub fn toInt64<'l>(obj: &LeanBound<'l, Self>) -> i64 {
        unsafe { ffi::inline::lean_float32_to_int64(Self::to_f32(obj)) }
    }

    /// Convert Float32 to ISize (with NaN check and bounds clamping).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.toISize` in Lean4.
    #[allow(non_snake_case)]
    pub fn toISize<'l>(obj: &LeanBound<'l, Self>) -> isize {
        unsafe { ffi::inline::lean_float32_to_isize(Self::to_f32(obj)) }
    }

    // ========================================================================
    // Decidable comparison methods
    // ========================================================================

    /// Decidable less than comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.decLt` in Lean4.
    #[allow(non_snake_case)]
    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float32_decLt(Self::to_f32(a), Self::to_f32(b)) != 0 }
    }

    /// Decidable less than or equal comparison.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Float32.decLe` in Lean4.
    #[allow(non_snake_case)]
    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::float::lean_float32_decLe(Self::to_f32(a), Self::to_f32(b)) != 0 }
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanFloat32> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanFloat32({})", LeanFloat32::to_f32(self))
    }
}
