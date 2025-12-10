//! Comprehensive conversion tests for UInt, SInt, Float, and Nat types.
//!
//! This test suite covers all conversion paths between:
//! - UInt types (UInt8, UInt16, UInt32, UInt64, USize)
//! - SInt types (Int8, Int16, Int32, Int64, ISize)
//! - Float types (Float, Float32)
//! - Nat type (arbitrary precision natural number)
//! - Int type (arbitrary precision integer)

use leo3::prelude::*;

// =============================================================================
// UInt ↔ UInt Conversions
// =============================================================================

#[test]
fn test_uint_widening_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 → UInt16 → UInt32 → UInt64
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let u16_val = LeanUInt8::toUInt16(&u8_val, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 42);

        let u32_val = LeanUInt16::toUInt32(&u16_val, lean)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 42);

        let u64_val = LeanUInt32::toUInt64(&u32_val, lean)?;
        assert_eq!(LeanUInt64::to_u64(&u64_val), 42);

        // Test max values
        let u8_max = LeanUInt8::mk(lean, u8::MAX)?;
        let u16_from_max = LeanUInt8::toUInt16(&u8_max, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_from_max), u8::MAX as u16);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_narrowing_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt64 → UInt32 → UInt16 → UInt8 (with truncation)
        let u64_val = LeanUInt64::mk(lean, 42)?;
        let u32_val = LeanUInt64::toUInt32(&u64_val, lean)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 42);

        let u16_val = LeanUInt32::toUInt16(&u32_val, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 42);

        let u8_val = LeanUInt16::toUInt8(&u16_val, lean)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 42);

        // Test truncation: 256 (0x100) → 0 when converting to UInt8
        let u16_overflow = LeanUInt16::mk(lean, 256)?;
        let u8_truncated = LeanUInt16::toUInt8(&u16_overflow, lean)?;
        assert_eq!(LeanUInt8::to_u8(&u8_truncated), 0);

        // Test truncation: 65536 (0x10000) → 0 when converting to UInt16
        let u32_overflow = LeanUInt32::mk(lean, 65536)?;
        let u16_truncated = LeanUInt32::toUInt16(&u32_overflow, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_truncated), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_boundary_values() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Zero conversions
        let u8_zero = LeanUInt8::mk(lean, 0)?;
        let u16_zero = LeanUInt8::toUInt16(&u8_zero, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_zero), 0);

        // Max value conversions
        let u8_max = LeanUInt8::mk(lean, u8::MAX)?;
        let u32_from_max = LeanUInt8::toUInt32(&u8_max, lean)?;
        assert_eq!(LeanUInt32::to_u32(&u32_from_max), u8::MAX as u32);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// SInt ↔ SInt Conversions
// =============================================================================

#[test]
fn test_sint_widening_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive values: Int8 → Int16 → Int32 → Int64
        let i8_val = LeanInt8::mk(lean, 42)?;
        let i16_val = LeanInt8::toInt16(&i8_val, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_val), 42);

        let i32_val = LeanInt16::toInt32(&i16_val, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_val), 42);

        let i64_val = LeanInt32::toInt64(&i32_val, lean)?;
        assert_eq!(LeanInt64::to_i64(&i64_val), 42);

        // Negative values: Int8 → Int16 → Int32 → Int64
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let i16_neg = LeanInt8::toInt16(&i8_neg, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_neg), -42);

        let i32_neg = LeanInt16::toInt32(&i16_neg, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_neg), -42);

        let i64_neg = LeanInt32::toInt64(&i32_neg, lean)?;
        assert_eq!(LeanInt64::to_i64(&i64_neg), -42);

        // Test min/max values
        let i8_min = LeanInt8::mk(lean, i8::MIN)?;
        let i16_from_min = LeanInt8::toInt16(&i8_min, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_from_min), i8::MIN as i16);

        let i8_max = LeanInt8::mk(lean, i8::MAX)?;
        let i16_from_max = LeanInt8::toInt16(&i8_max, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_from_max), i8::MAX as i16);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_narrowing_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive values: Int64 → Int32 → Int16 → Int8
        let i64_val = LeanInt64::mk(lean, 42)?;
        let i32_val = LeanInt64::toInt32(&i64_val, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_val), 42);

        let i16_val = LeanInt32::toInt16(&i32_val, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_val), 42);

        let i8_val = LeanInt16::toInt8(&i16_val, lean)?;
        assert_eq!(LeanInt8::to_i8(&i8_val), 42);

        // Negative values
        let i64_neg = LeanInt64::mk(lean, -42)?;
        let i32_neg = LeanInt64::toInt32(&i64_neg, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_neg), -42);

        let i16_neg = LeanInt32::toInt16(&i32_neg, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_neg), -42);

        let i8_neg = LeanInt16::toInt8(&i16_neg, lean)?;
        assert_eq!(LeanInt8::to_i8(&i8_neg), -42);

        // Test truncation with overflow
        let i16_overflow = LeanInt16::mk(lean, 128)?;
        let i8_truncated = LeanInt16::toInt8(&i16_overflow, lean)?;
        assert_eq!(LeanInt8::to_i8(&i8_truncated), -128); // Wraps around

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_boundary_values() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Zero
        let i8_zero = LeanInt8::mk(lean, 0)?;
        let i32_zero = LeanInt8::toInt32(&i8_zero, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_zero), 0);

        // -1 (all bits set)
        let i8_neg_one = LeanInt8::mk(lean, -1)?;
        let i32_neg_one = LeanInt8::toInt32(&i8_neg_one, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_neg_one), -1);

        // Min value
        let i8_min = LeanInt8::mk(lean, i8::MIN)?;
        let i32_min = LeanInt8::toInt32(&i8_min, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_min), i8::MIN as i32);

        // Max value
        let i8_max = LeanInt8::mk(lean, i8::MAX)?;
        let i32_max = LeanInt8::toInt32(&i8_max, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_max), i8::MAX as i32);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Float ↔ UInt Conversions
// =============================================================================

#[test]
fn test_uint_to_float_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 → Float
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let float_val = LeanUInt8::toFloat(&u8_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 42.0);

        // UInt16 → Float
        let u16_val = LeanUInt16::mk(lean, 1000)?;
        let float_val = LeanUInt16::toFloat(&u16_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 1000.0);

        // UInt32 → Float
        let u32_val = LeanUInt32::mk(lean, 100000)?;
        let float_val = LeanUInt32::toFloat(&u32_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 100000.0);

        // UInt64 → Float
        let u64_val = LeanUInt64::mk(lean, 1000000)?;
        let float_val = LeanUInt64::toFloat(&u64_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 1000000.0);

        // Test max values
        let u8_max = LeanUInt8::mk(lean, u8::MAX)?;
        let float_max = LeanUInt8::toFloat(&u8_max, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_max), u8::MAX as f64);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_to_float32_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 → Float32
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let float32_val = LeanUInt8::toFloat32(&u8_val, lean)?;
        assert_eq!(LeanFloat32::to_f32(&float32_val), 42.0_f32);

        // UInt16 → Float32
        let u16_val = LeanUInt16::mk(lean, 1000)?;
        let float32_val = LeanUInt16::toFloat32(&u16_val, lean)?;
        assert_eq!(LeanFloat32::to_f32(&float32_val), 1000.0_f32);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_float_to_uint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Float → UInt8
        let float_val = LeanFloat::from_f64(lean, 42.0)?;
        let u8_val = LeanFloat::toUInt8(&float_val);
        assert_eq!(u8_val, 42);

        // Float → UInt16
        let u16_val = LeanFloat::toUInt16(&float_val);
        assert_eq!(u16_val, 42);

        // Float → UInt32
        let u32_val = LeanFloat::toUInt32(&float_val);
        assert_eq!(u32_val, 42);

        // Float → UInt64
        let u64_val = LeanFloat::toUInt64(&float_val);
        assert_eq!(u64_val, 42);

        // Test with fractional values (should truncate)
        let float_frac = LeanFloat::from_f64(lean, 42.7)?;
        let u8_trunc = LeanFloat::toUInt8(&float_frac);
        assert_eq!(u8_trunc, 42);

        // Test with zero
        let float_zero = LeanFloat::from_f64(lean, 0.0)?;
        let u8_zero = LeanFloat::toUInt8(&float_zero);
        assert_eq!(u8_zero, 0);

        // Test with negative (should clamp to 0)
        let float_neg = LeanFloat::from_f64(lean, -5.0)?;
        let u8_neg = LeanFloat::toUInt8(&float_neg);
        assert_eq!(u8_neg, 0);

        // Test with overflow (should clamp to max)
        let float_overflow = LeanFloat::from_f64(lean, 300.0)?;
        let u8_overflow = LeanFloat::toUInt8(&float_overflow);
        assert_eq!(u8_overflow, u8::MAX);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_float_uint_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: UInt → Float → UInt
        let original = LeanUInt16::mk(lean, 12345)?;
        let as_float = LeanUInt16::toFloat(&original, lean)?;
        let back_to_uint = LeanFloat::toUInt16(&as_float);
        assert_eq!(back_to_uint, 12345);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Float ↔ SInt Conversions
// =============================================================================

#[test]
fn test_sint_to_float_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive Int8 → Float
        let i8_pos = LeanInt8::mk(lean, 42)?;
        let float_pos = LeanInt8::toFloat(&i8_pos, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_pos), 42.0);

        // Negative Int8 → Float
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let float_neg = LeanInt8::toFloat(&i8_neg, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_neg), -42.0);

        // Int16 → Float
        let i16_val = LeanInt16::mk(lean, -1000)?;
        let float_val = LeanInt16::toFloat(&i16_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), -1000.0);

        // Int32 → Float
        let i32_val = LeanInt32::mk(lean, 100000)?;
        let float_val = LeanInt32::toFloat(&i32_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 100000.0);

        // Int64 → Float
        let i64_val = LeanInt64::mk(lean, -1000000)?;
        let float_val = LeanInt64::toFloat(&i64_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), -1000000.0);

        // Test min/max values
        let i8_min = LeanInt8::mk(lean, i8::MIN)?;
        let float_min = LeanInt8::toFloat(&i8_min, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_min), i8::MIN as f64);

        let i8_max = LeanInt8::mk(lean, i8::MAX)?;
        let float_max = LeanInt8::toFloat(&i8_max, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_max), i8::MAX as f64);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_to_float32_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive Int8 → Float32
        let i8_pos = LeanInt8::mk(lean, 42)?;
        let float32_pos = LeanInt8::toFloat32(&i8_pos, lean)?;
        assert_eq!(LeanFloat32::to_f32(&float32_pos), 42.0_f32);

        // Negative Int8 → Float32
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let float32_neg = LeanInt8::toFloat32(&i8_neg, lean)?;
        assert_eq!(LeanFloat32::to_f32(&float32_neg), -42.0_f32);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_float_to_sint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive Float → Int8
        let float_pos = LeanFloat::from_f64(lean, 42.0)?;
        let i8_pos = LeanFloat::toInt8(&float_pos);
        assert_eq!(i8_pos, 42);

        // Negative Float → Int8
        let float_neg = LeanFloat::from_f64(lean, -42.0)?;
        let i8_neg = LeanFloat::toInt8(&float_neg);
        assert_eq!(i8_neg, -42);

        // Float → Int16
        let i16_neg = LeanFloat::toInt16(&float_neg);
        assert_eq!(i16_neg, -42);

        // Float → Int32
        let i32_neg = LeanFloat::toInt32(&float_neg);
        assert_eq!(i32_neg, -42);

        // Float → Int64
        let i64_neg = LeanFloat::toInt64(&float_neg);
        assert_eq!(i64_neg, -42);

        // Test with fractional values (should truncate towards zero)
        let float_frac_pos = LeanFloat::from_f64(lean, 42.7)?;
        let i8_trunc_pos = LeanFloat::toInt8(&float_frac_pos);
        assert_eq!(i8_trunc_pos, 42);

        let float_frac_neg = LeanFloat::from_f64(lean, -42.7)?;
        let i8_trunc_neg = LeanFloat::toInt8(&float_frac_neg);
        assert_eq!(i8_trunc_neg, -42);

        // Test with zero
        let float_zero = LeanFloat::from_f64(lean, 0.0)?;
        let i8_zero = LeanFloat::toInt8(&float_zero);
        assert_eq!(i8_zero, 0);

        // Test with overflow (should clamp)
        let float_overflow_pos = LeanFloat::from_f64(lean, 200.0)?;
        let i8_overflow_pos = LeanFloat::toInt8(&float_overflow_pos);
        assert_eq!(i8_overflow_pos, i8::MAX);

        let float_overflow_neg = LeanFloat::from_f64(lean, -200.0)?;
        let i8_overflow_neg = LeanFloat::toInt8(&float_overflow_neg);
        assert_eq!(i8_overflow_neg, i8::MIN);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_float_sint_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: SInt → Float → SInt (positive)
        let original_pos = LeanInt16::mk(lean, 12345)?;
        let as_float = LeanInt16::toFloat(&original_pos, lean)?;
        let back_to_int = LeanFloat::toInt16(&as_float);
        assert_eq!(back_to_int, 12345);

        // Round-trip: SInt → Float → SInt (negative)
        let original_neg = LeanInt16::mk(lean, -12345)?;
        let as_float = LeanInt16::toFloat(&original_neg, lean)?;
        let back_to_int = LeanFloat::toInt16(&as_float);
        assert_eq!(back_to_int, -12345);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Nat ↔ UInt Conversions
// =============================================================================

#[test]
fn test_nat_to_uint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Small Nat → various UInts
        let nat = LeanNat::from_usize(lean, 42)?;

        let u8_val = LeanNat::toUInt8(&nat)?;
        assert_eq!(u8_val, 42);

        let u16_val = LeanNat::toUInt16(&nat)?;
        assert_eq!(u16_val, 42);

        let u32_val = LeanNat::toUInt32(&nat)?;
        assert_eq!(u32_val, 42);

        let u64_val = LeanNat::toUInt64(&nat)?;
        assert_eq!(u64_val, 42);

        let usize_val = LeanNat::toUSize(&nat)?;
        assert_eq!(usize_val, 42);

        // Test with zero
        let nat_zero = LeanNat::from_usize(lean, 0)?;
        assert_eq!(LeanNat::toUInt8(&nat_zero)?, 0);

        // Test with max UInt8 value
        let nat_max_u8 = LeanNat::from_usize(lean, u8::MAX as usize)?;
        assert_eq!(LeanNat::toUInt8(&nat_max_u8)?, u8::MAX);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_to_nat_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 → Nat
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let nat = LeanUInt8::toNat(&u8_val, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 42);

        // UInt16 → Nat
        let u16_val = LeanUInt16::mk(lean, 1000)?;
        let nat = LeanUInt16::toNat(&u16_val, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 1000);

        // UInt32 → Nat
        let u32_val = LeanUInt32::mk(lean, 100000)?;
        let nat = LeanUInt32::toNat(&u32_val, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 100000);

        // UInt64 → Nat
        let u64_val = LeanUInt64::mk(lean, 1000000)?;
        let nat = LeanUInt64::toNat(&u64_val, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 1000000);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_uint_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: UInt → Nat → UInt
        let original = LeanUInt16::mk(lean, 12345)?;
        let as_nat = LeanUInt16::toNat(&original, lean)?;
        let back_u16 = LeanNat::toUInt16(&as_nat)?;
        assert_eq!(back_u16, 12345);

        // Round-trip: Nat → UInt → Nat
        let original_nat = LeanNat::from_usize(lean, 54321)?;
        let as_uint = LeanUInt32::ofNat(lean, &original_nat)?;
        let back_nat = LeanUInt32::toNat(&as_uint, lean)?;
        assert_eq!(LeanNat::to_usize(&back_nat)?, 54321);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_ofnat_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let nat = LeanNat::from_usize(lean, 42)?;

        // UInt8::ofNat
        let u8_val = LeanUInt8::ofNat(lean, &nat)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 42);

        // UInt16::ofNat
        let u16_val = LeanUInt16::ofNat(lean, &nat)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 42);

        // UInt32::ofNat
        let u32_val = LeanUInt32::ofNat(lean, &nat)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 42);

        // UInt64::ofNat
        let u64_val = LeanUInt64::ofNat(lean, &nat)?;
        assert_eq!(LeanUInt64::to_u64(&u64_val), 42);

        // Test truncation with overflow
        let nat_overflow = LeanNat::from_usize(lean, 256)?;
        let u8_truncated = LeanUInt8::ofNat(lean, &nat_overflow)?;
        assert_eq!(LeanUInt8::to_u8(&u8_truncated), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Nat ↔ SInt Conversions
// =============================================================================

#[test]
fn test_nat_to_sint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Small positive Nat → various SInts
        let nat = LeanNat::from_usize(lean, 42)?;

        // Int8::ofNat
        let i8_val = LeanInt8::ofNat(lean, &nat)?;
        assert_eq!(LeanInt8::to_i8(&i8_val), 42);

        // Int16::ofNat
        let i16_val = LeanInt16::ofNat(lean, &nat)?;
        assert_eq!(LeanInt16::to_i16(&i16_val), 42);

        // Int32::ofNat
        let i32_val = LeanInt32::ofNat(lean, &nat)?;
        assert_eq!(LeanInt32::to_i32(&i32_val), 42);

        // Int64::ofNat
        let i64_val = LeanInt64::ofNat(lean, &nat)?;
        assert_eq!(LeanInt64::to_i64(&i64_val), 42);

        // Test with zero
        let nat_zero = LeanNat::from_usize(lean, 0)?;
        let i8_zero = LeanInt8::ofNat(lean, &nat_zero)?;
        assert_eq!(LeanInt8::to_i8(&i8_zero), 0);

        // Test truncation: value > i8::MAX wraps around
        let nat_overflow = LeanNat::from_usize(lean, 128)?;
        let i8_wrapped = LeanInt8::ofNat(lean, &nat_overflow)?;
        assert_eq!(LeanInt8::to_i8(&i8_wrapped), -128);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_to_nat_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive Int8 → Nat (should succeed)
        let i8_pos = LeanInt8::mk(lean, 42)?;
        let nat = LeanInt8::toNat(&i8_pos, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 42);

        // Positive Int16 → Nat
        let i16_pos = LeanInt16::mk(lean, 1000)?;
        let nat = LeanInt16::toNat(&i16_pos, lean)?;
        assert_eq!(LeanNat::to_usize(&nat)?, 1000);

        // Zero → Nat
        let i8_zero = LeanInt8::mk(lean, 0)?;
        let nat_zero = LeanInt8::toNat(&i8_zero, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_zero)?, 0);

        // Negative Int8 → Nat (should fail)
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let result_neg = LeanInt8::toNat(&i8_neg, lean);
        assert!(result_neg.is_err());

        // Negative Int16 → Nat (should fail)
        let i16_neg = LeanInt16::mk(lean, -1000)?;
        let result_neg = LeanInt16::toNat(&i16_neg, lean);
        assert!(result_neg.is_err());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_nat_positive_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: positive SInt → Nat → SInt
        let original = LeanInt16::mk(lean, 12345)?;
        let as_nat = LeanInt16::toNat(&original, lean)?;
        let back_int = LeanInt16::ofNat(lean, &as_nat)?;
        assert_eq!(LeanInt16::to_i16(&back_int), 12345);

        // Round-trip: Nat → SInt → Nat
        let original_nat = LeanNat::from_usize(lean, 54321)?;
        let as_int = LeanInt32::ofNat(lean, &original_nat)?;
        let back_nat = LeanInt32::toNat(&as_int, lean)?;
        assert_eq!(LeanNat::to_usize(&back_nat)?, 54321);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Float ↔ Nat Conversions
// =============================================================================

#[test]
fn test_nat_to_float_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Small Nat → Float
        let nat_small = LeanNat::from_usize(lean, 42)?;
        let float_val = LeanFloat::ofNat(&nat_small, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 42.0);

        // Large Nat → Float
        let nat_large = LeanNat::from_usize(lean, 1000000)?;
        let float_large = LeanFloat::ofNat(&nat_large, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_large), 1000000.0);

        // Zero
        let nat_zero = LeanNat::from_usize(lean, 0)?;
        let float_zero = LeanFloat::ofNat(&nat_zero, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_zero), 0.0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_float_to_nat_via_uint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Float → UInt → Nat
        let float_val = LeanFloat::from_f64(lean, 42.5)?;
        let uint_val = LeanFloat::toUInt32(&float_val);
        let nat_from_float = LeanNat::from_usize(lean, uint_val as usize)?;
        assert_eq!(LeanNat::to_usize(&nat_from_float)?, 42);

        // Negative float should clamp to 0
        let float_neg = LeanFloat::from_f64(lean, -10.0)?;
        let uint_neg = LeanFloat::toUInt32(&float_neg);
        let nat_from_neg = LeanNat::from_usize(lean, uint_neg as usize)?;
        assert_eq!(LeanNat::to_usize(&nat_from_neg)?, 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_float_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: Nat → Float → Nat (via UInt)
        let original_nat = LeanNat::from_usize(lean, 12345)?;
        let as_float = LeanFloat::ofNat(&original_nat, lean)?;
        let as_uint = LeanFloat::toUInt32(&as_float);
        let back_nat = LeanNat::from_usize(lean, as_uint as usize)?;
        assert_eq!(LeanNat::to_usize(&back_nat)?, 12345);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Cross-Type Conversions (UInt ↔ SInt)
// =============================================================================

#[test]
fn test_uint_sint_cross_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt → Nat → SInt
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let nat = LeanUInt8::toNat(&u8_val, lean)?;
        let i8_val = LeanInt8::ofNat(lean, &nat)?;
        assert_eq!(LeanInt8::to_i8(&i8_val), 42);

        // SInt → Nat → UInt (positive value)
        let i16_pos = LeanInt16::mk(lean, 100)?;
        let nat_pos = LeanInt16::toNat(&i16_pos, lean)?;
        let u16_val = LeanUInt16::ofNat(lean, &nat_pos)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 100);

        // SInt → Nat fails for negative
        let i16_neg = LeanInt16::mk(lean, -100)?;
        let nat_neg_result = LeanInt16::toNat(&i16_neg, lean);
        assert!(nat_neg_result.is_err());

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// Edge Cases and Special Values
// =============================================================================

#[test]
fn test_float_special_values() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // NaN → UInt (should return 0)
        let nan = LeanFloat::nan(lean)?;
        assert!(LeanFloat::isNaN(&nan));
        let nan_to_uint = LeanFloat::toUInt8(&nan);
        assert_eq!(nan_to_uint, 0);

        // Infinity → UInt (should clamp to max)
        let inf = LeanFloat::infinity(lean)?;
        assert!(LeanFloat::isInf(&inf));
        let inf_to_uint = LeanFloat::toUInt8(&inf);
        assert_eq!(inf_to_uint, u8::MAX);

        // Negative Infinity → UInt (should clamp to 0)
        let neg_inf = LeanFloat::neg_infinity(lean)?;
        let neg_inf_to_uint = LeanFloat::toUInt8(&neg_inf);
        assert_eq!(neg_inf_to_uint, 0);

        // NaN → SInt (should return 0)
        let nan_to_sint = LeanFloat::toInt8(&nan);
        assert_eq!(nan_to_sint, 0);

        // Positive Infinity → SInt (should clamp to max)
        let inf_to_sint = LeanFloat::toInt8(&inf);
        assert_eq!(inf_to_sint, i8::MAX);

        // Negative Infinity → SInt (should clamp to min)
        let neg_inf_to_sint = LeanFloat::toInt8(&neg_inf);
        assert_eq!(neg_inf_to_sint, i8::MIN);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_zero_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Zero through all type paths
        let nat_zero = LeanNat::from_usize(lean, 0)?;
        let u8_zero = LeanUInt8::ofNat(lean, &nat_zero)?;
        let i8_zero = LeanInt8::ofNat(lean, &nat_zero)?;
        let float_zero = LeanFloat::ofNat(&nat_zero, lean)?;

        assert_eq!(LeanUInt8::to_u8(&u8_zero), 0);
        assert_eq!(LeanInt8::to_i8(&i8_zero), 0);
        assert_eq!(LeanFloat::to_f64(&float_zero), 0.0);

        // Back to Nat
        let nat_from_u8 = LeanUInt8::toNat(&u8_zero, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_from_u8)?, 0);

        let nat_from_i8 = LeanInt8::toNat(&i8_zero, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_from_i8)?, 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_max_min_boundary_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 MAX
        let u8_max = LeanUInt8::mk(lean, u8::MAX)?;
        let nat_max = LeanUInt8::toNat(&u8_max, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_max)?, u8::MAX as usize);

        let u16_from_max = LeanUInt8::toUInt16(&u8_max, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_from_max), u8::MAX as u16);

        // Int8 MIN
        let i8_min = LeanInt8::mk(lean, i8::MIN)?;
        let float_min = LeanInt8::toFloat(&i8_min, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_min), i8::MIN as f64);

        // Int8 MAX
        let i8_max = LeanInt8::mk(lean, i8::MAX)?;
        let nat_from_max = LeanInt8::toNat(&i8_max, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_from_max)?, i8::MAX as usize);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// UInt ↔ LeanInt (Arbitrary Precision Integer) Conversions
// =============================================================================

#[test]
fn test_uint_to_leanint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // UInt8 → LeanInt
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let int_val = LeanUInt8::toInt(&u8_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(42));

        // UInt16 → LeanInt
        let u16_val = LeanUInt16::mk(lean, 1000)?;
        let int_val = LeanUInt16::toInt(&u16_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(1000));

        // UInt32 → LeanInt
        let u32_val = LeanUInt32::mk(lean, 100000)?;
        let int_val = LeanUInt32::toInt(&u32_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(100000));

        // UInt64 → LeanInt
        let u64_val = LeanUInt64::mk(lean, 1000000)?;
        let int_val = LeanUInt64::toInt(&u64_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(1000000));

        // Test with zero
        let u8_zero = LeanUInt8::mk(lean, 0)?;
        let int_zero = LeanUInt8::toInt(&u8_zero, lean)?;
        assert_eq!(LeanInt::to_i64(&int_zero), Some(0));

        // Test with max UInt8
        let u8_max = LeanUInt8::mk(lean, u8::MAX)?;
        let int_max = LeanUInt8::toInt(&u8_max, lean)?;
        assert_eq!(LeanInt::to_i64(&int_max), Some(u8::MAX as i64));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_leanint_to_uint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive LeanInt → UInt8
        let int_val = LeanInt::from_i64(lean, 42)?;
        let u8_val = LeanUInt8::ofInt(lean, &int_val)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 42);

        // Positive LeanInt → UInt16
        let u16_val = LeanUInt16::ofInt(lean, &int_val)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 42);

        // Positive LeanInt → UInt32
        let u32_val = LeanUInt32::ofInt(lean, &int_val)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 42);

        // Positive LeanInt → UInt64
        let u64_val = LeanUInt64::ofInt(lean, &int_val)?;
        assert_eq!(LeanUInt64::to_u64(&u64_val), 42);

        // Negative LeanInt → UInt (wraps around in two's complement)
        let int_neg = LeanInt::from_i64(lean, -1)?;
        let u8_neg = LeanUInt8::ofInt(lean, &int_neg)?;
        assert_eq!(LeanUInt8::to_u8(&u8_neg), 255); // -1 wraps to 255 in u8

        // Zero
        let int_zero = LeanInt::from_i64(lean, 0)?;
        let u8_zero = LeanUInt8::ofInt(lean, &int_zero)?;
        assert_eq!(LeanUInt8::to_u8(&u8_zero), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_uint_leanint_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: UInt → LeanInt → UInt
        let original = LeanUInt16::mk(lean, 12345)?;
        let as_int = LeanUInt16::toInt(&original, lean)?;
        let back_uint = LeanUInt16::ofInt(lean, &as_int)?;
        assert_eq!(LeanUInt16::to_u16(&back_uint), 12345);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// SInt ↔ LeanInt (Arbitrary Precision Integer) Conversions
// =============================================================================

#[test]
fn test_sint_to_leanint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive Int8 → LeanInt
        let i8_pos = LeanInt8::mk(lean, 42)?;
        let int_pos = LeanInt8::toInt(&i8_pos, lean)?;
        assert_eq!(LeanInt::to_i64(&int_pos), Some(42));

        // Negative Int8 → LeanInt
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let int_neg = LeanInt8::toInt(&i8_neg, lean)?;
        assert_eq!(LeanInt::to_i64(&int_neg), Some(-42));

        // Int16 → LeanInt
        let i16_val = LeanInt16::mk(lean, -1000)?;
        let int_val = LeanInt16::toInt(&i16_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(-1000));

        // Int32 → LeanInt
        let i32_val = LeanInt32::mk(lean, 100000)?;
        let int_val = LeanInt32::toInt(&i32_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(100000));

        // Int64 → LeanInt
        let i64_val = LeanInt64::mk(lean, -1000000)?;
        let int_val = LeanInt64::toInt(&i64_val, lean)?;
        assert_eq!(LeanInt::to_i64(&int_val), Some(-1000000));

        // Test with min/max values
        let i8_min = LeanInt8::mk(lean, i8::MIN)?;
        let int_min = LeanInt8::toInt(&i8_min, lean)?;
        assert_eq!(LeanInt::to_i64(&int_min), Some(i8::MIN as i64));

        let i8_max = LeanInt8::mk(lean, i8::MAX)?;
        let int_max = LeanInt8::toInt(&i8_max, lean)?;
        assert_eq!(LeanInt::to_i64(&int_max), Some(i8::MAX as i64));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_leanint_to_sint_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive LeanInt → Int8
        let int_pos = LeanInt::from_i64(lean, 42)?;
        let i8_pos = LeanInt8::ofInt(lean, &int_pos)?;
        assert_eq!(LeanInt8::to_i8(&i8_pos), 42);

        // Negative LeanInt → Int8
        let int_neg = LeanInt::from_i64(lean, -42)?;
        let i8_neg = LeanInt8::ofInt(lean, &int_neg)?;
        assert_eq!(LeanInt8::to_i8(&i8_neg), -42);

        // LeanInt → Int16
        let i16_neg = LeanInt16::ofInt(lean, &int_neg)?;
        assert_eq!(LeanInt16::to_i16(&i16_neg), -42);

        // LeanInt → Int32
        let i32_neg = LeanInt32::ofInt(lean, &int_neg)?;
        assert_eq!(LeanInt32::to_i32(&i32_neg), -42);

        // LeanInt → Int64
        let i64_neg = LeanInt64::ofInt(lean, &int_neg)?;
        assert_eq!(LeanInt64::to_i64(&i64_neg), -42);

        // Zero
        let int_zero = LeanInt::from_i64(lean, 0)?;
        let i8_zero = LeanInt8::ofInt(lean, &int_zero)?;
        assert_eq!(LeanInt8::to_i8(&i8_zero), 0);

        // Test truncation with overflow
        let int_overflow = LeanInt::from_i64(lean, 200)?;
        let i8_overflow = LeanInt8::ofInt(lean, &int_overflow)?;
        assert_eq!(LeanInt8::to_i8(&i8_overflow), -56); // 200 truncates to -56 in i8

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_sint_leanint_round_trip() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Round-trip: SInt → LeanInt → SInt (positive)
        let original_pos = LeanInt16::mk(lean, 12345)?;
        let as_int = LeanInt16::toInt(&original_pos, lean)?;
        let back_sint = LeanInt16::ofInt(lean, &as_int)?;
        assert_eq!(LeanInt16::to_i16(&back_sint), 12345);

        // Round-trip: SInt → LeanInt → SInt (negative)
        let original_neg = LeanInt16::mk(lean, -12345)?;
        let as_int = LeanInt16::toInt(&original_neg, lean)?;
        let back_sint = LeanInt16::ofInt(lean, &as_int)?;
        assert_eq!(LeanInt16::to_i16(&back_sint), -12345);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// LeanInt ↔ Nat Conversions
// =============================================================================

#[test]
fn test_leanint_nat_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Positive LeanInt → Nat (via ofNat construction)
        let nat = LeanNat::from_usize(lean, 42)?;
        let int_from_nat = LeanInt::ofNat(lean, nat)?;
        assert_eq!(LeanInt::to_i64(&int_from_nat), Some(42));

        // LeanInt → Nat not directly supported, but can go through SInt
        let int_val = LeanInt::from_i64(lean, 100)?;
        let i32_val = LeanInt32::ofInt(lean, &int_val)?;
        let nat_from_int = LeanInt32::toNat(&i32_val, lean)?;
        assert_eq!(LeanNat::to_usize(&nat_from_int)?, 100);

        Ok(())
    });

    assert!(result.is_ok());
}

// =============================================================================
// LeanInt ↔ Float Conversions
// =============================================================================

#[test]
fn test_leanint_float_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // LeanInt → Float (via ofInt)
        let int_pos = LeanInt::from_i64(lean, 42)?;
        let float_pos = LeanFloat::ofInt(&int_pos, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_pos), 42.0);

        let int_neg = LeanInt::from_i64(lean, -1000)?;
        let float_neg = LeanFloat::ofInt(&int_neg, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_neg), -1000.0);

        // Large values
        let int_large = LeanInt::from_i64(lean, 1000000)?;
        let float_large = LeanFloat::ofInt(&int_large, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_large), 1000000.0);

        // Zero
        let int_zero = LeanInt::from_i64(lean, 0)?;
        let float_zero = LeanFloat::ofInt(&int_zero, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_zero), 0.0);

        Ok(())
    });

    assert!(result.is_ok());
}
