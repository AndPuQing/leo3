//! Tests for fixed-precision integer API functions (constants, comparisons, character conversions)

#![allow(non_snake_case)]

use leo3::prelude::*;

#[test]
fn test_uint8_constants() {
    assert_eq!(LeanUInt8::SIZE, 256);
    assert_eq!(LeanUInt8::MIN, 0);
    assert_eq!(LeanUInt8::MAX, 255);
}

#[test]
fn test_uint16_constants() {
    assert_eq!(LeanUInt16::SIZE, 65536);
    assert_eq!(LeanUInt16::MIN, 0);
    assert_eq!(LeanUInt16::MAX, 65535);
}

#[test]
fn test_uint32_constants() {
    assert_eq!(LeanUInt32::SIZE, 4294967296);
    assert_eq!(LeanUInt32::MIN, 0);
    assert_eq!(LeanUInt32::MAX, 4294967295);
}

#[test]
fn test_uint64_constants() {
    assert_eq!(LeanUInt64::SIZE, 18446744073709551616);
    assert_eq!(LeanUInt64::MIN, 0);
    assert_eq!(LeanUInt64::MAX, 18446744073709551615);
}

#[test]
fn test_int8_constants() {
    assert_eq!(LeanInt8::SIZE, 256);
    assert_eq!(LeanInt8::MIN, -128);
    assert_eq!(LeanInt8::MAX, 127);
}

#[test]
fn test_int16_constants() {
    assert_eq!(LeanInt16::SIZE, 65536);
    assert_eq!(LeanInt16::MIN, -32768);
    assert_eq!(LeanInt16::MAX, 32767);
}

#[test]
fn test_int32_constants() {
    assert_eq!(LeanInt32::SIZE, 4294967296);
    assert_eq!(LeanInt32::MIN, -2147483648);
    assert_eq!(LeanInt32::MAX, 2147483647);
}

#[test]
fn test_int64_constants() {
    assert_eq!(LeanInt64::SIZE, 18446744073709551616);
    assert_eq!(LeanInt64::MIN, -9223372036854775808);
    assert_eq!(LeanInt64::MAX, 9223372036854775807);
}

#[test]
fn test_uint8_comparisons() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanUInt8::mk(lean, 42)?;
        let b = LeanUInt8::mk(lean, 42)?;
        let c = LeanUInt8::mk(lean, 100)?;

        assert!(LeanUInt8::decEq(&a, &b));
        assert!(!LeanUInt8::decEq(&a, &c));

        assert!(LeanUInt8::decLt(&a, &c));
        assert!(!LeanUInt8::decLt(&c, &a));
        assert!(!LeanUInt8::decLt(&a, &b));

        assert!(LeanUInt8::decLe(&a, &c));
        assert!(LeanUInt8::decLe(&a, &b));
        assert!(!LeanUInt8::decLe(&c, &a));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_comparisons() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt8::mk(lean, -42)?;
        let b = LeanInt8::mk(lean, -42)?;
        let c = LeanInt8::mk(lean, 100)?;

        assert!(LeanInt8::decEq(&a, &b));
        assert!(!LeanInt8::decEq(&a, &c));

        assert!(LeanInt8::decLt(&a, &c));
        assert!(!LeanInt8::decLt(&c, &a));
        assert!(!LeanInt8::decLt(&a, &b));

        assert!(LeanInt8::decLe(&a, &c));
        assert!(LeanInt8::decLe(&a, &b));
        assert!(!LeanInt8::decLe(&c, &a));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint8_to_char() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // All UInt8 values are valid Unicode scalars
        let val = LeanUInt8::mk(lean, 65)?; // 'A'
        assert!(LeanUInt8::isValidChar(&val));

        let c = LeanUInt8::toChar(&val, lean)?;
        assert_eq!(LeanChar::toChar(&c), Some('A'));

        let val = LeanUInt8::mk(lean, 255)?;
        assert!(LeanUInt8::isValidChar(&val));
        let c = LeanUInt8::toChar(&val, lean)?;
        assert_eq!(LeanChar::to_u32(&c), 255);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint32_to_char() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Valid Unicode scalar
        let val = LeanUInt32::mk(lean, 0x1F600)?; // 😀
        assert!(LeanUInt32::isValidChar(&val));
        let c = LeanUInt32::toChar(&val, lean)?;
        assert_eq!(LeanChar::to_u32(&c), 0x1F600);

        // Invalid Unicode scalar (surrogate range)
        let val = LeanUInt32::mk(lean, 0xD800)?;
        assert!(!LeanUInt32::isValidChar(&val));
        assert!(LeanUInt32::toChar(&val, lean).is_err());

        // Invalid Unicode scalar (too large)
        let val = LeanUInt32::mk(lean, 0x110000)?;
        assert!(!LeanUInt32::isValidChar(&val));
        assert!(LeanUInt32::toChar(&val, lean).is_err());

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_to_char() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Positive values
        let val = LeanInt8::mk(lean, 65)?; // 'A'
        assert!(LeanInt8::isValidChar(&val));
        let c = LeanInt8::toChar(&val, lean)?;
        assert_eq!(LeanChar::toChar(&c), Some('A'));

        // Negative values should fail
        let val = LeanInt8::mk(lean, -42)?;
        assert!(!LeanInt8::isValidChar(&val));
        assert!(LeanInt8::toChar(&val, lean).is_err());

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int32_abs() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let val = LeanInt32::mk(lean, -42)?;
        let abs_val = LeanInt32::abs(lean, &val)?;
        assert_eq!(LeanInt32::to_i32(&abs_val), 42);

        let val = LeanInt32::mk(lean, 42)?;
        let abs_val = LeanInt32::abs(lean, &val)?;
        assert_eq!(LeanInt32::to_i32(&abs_val), 42);

        // Edge case: MIN value wraps
        let val = LeanInt32::mk(lean, LeanInt32::MIN)?;
        let abs_val = LeanInt32::abs(lean, &val)?;
        assert_eq!(LeanInt32::to_i32(&abs_val), LeanInt32::MIN);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint16_comparisons() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanUInt16::mk(lean, 1000)?;
        let b = LeanUInt16::mk(lean, 1000)?;
        let c = LeanUInt16::mk(lean, 2000)?;

        assert!(LeanUInt16::decEq(&a, &b));
        assert!(!LeanUInt16::decEq(&a, &c));

        assert!(LeanUInt16::decLt(&a, &c));
        assert!(!LeanUInt16::decLt(&c, &a));

        assert!(LeanUInt16::decLe(&a, &c));
        assert!(LeanUInt16::decLe(&a, &b));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int64_comparisons() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt64::mk(lean, -9000000000)?;
        let b = LeanInt64::mk(lean, -9000000000)?;
        let c = LeanInt64::mk(lean, 9000000000)?;

        assert!(LeanInt64::decEq(&a, &b));
        assert!(!LeanInt64::decEq(&a, &c));

        assert!(LeanInt64::decLt(&a, &c));
        assert!(!LeanInt64::decLt(&c, &a));

        assert!(LeanInt64::decLe(&a, &c));
        assert!(LeanInt64::decLe(&a, &b));

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int_toInt_ofInt() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test Int8
        let i8_val = LeanInt8::mk(lean, 42)?;
        let int_val = LeanInt8::toInt(&i8_val, lean)?;
        let i8_back = LeanInt8::ofInt(lean, &int_val)?;
        assert_eq!(LeanInt8::to_i8(&i8_back), 42);

        // Test negative
        let i8_neg = LeanInt8::mk(lean, -42)?;
        let int_neg = LeanInt8::toInt(&i8_neg, lean)?;
        let i8_neg_back = LeanInt8::ofInt(lean, &int_neg)?;
        assert_eq!(LeanInt8::to_i8(&i8_neg_back), -42);

        // Test Int32
        let i32_val = LeanInt32::mk(lean, 100000)?;
        let int_val32 = LeanInt32::toInt(&i32_val, lean)?;
        let i32_back = LeanInt32::ofInt(lean, &int_val32)?;
        assert_eq!(LeanInt32::to_i32(&i32_back), 100000);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int_toNat_ofNat() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test positive values
        let i8_val = LeanInt8::mk(lean, 42)?;
        let nat_val = LeanInt8::toNat(&i8_val, lean)?;
        let i8_back = LeanInt8::ofNat(lean, &nat_val)?;
        assert_eq!(LeanInt8::to_i8(&i8_back), 42);

        // Test that negative values fail
        let i8_neg = LeanInt8::mk(lean, -42)?;
        assert!(LeanInt8::toNat(&i8_neg, lean).is_err());

        // Test Int16
        let i16_val = LeanInt16::mk(lean, 1000)?;
        let nat_val16 = LeanInt16::toNat(&i16_val, lean)?;
        let i16_back = LeanInt16::ofNat(lean, &nat_val16)?;
        assert_eq!(LeanInt16::to_i16(&i16_back), 1000);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_toFloat() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test unsigned
        let u8_val = LeanUInt8::mk(lean, 42)?;
        let float_val = LeanUInt8::toFloat(&u8_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val), 42.0);

        let u32_val = LeanUInt32::mk(lean, 1000)?;
        let float_val32 = LeanUInt32::toFloat(&u32_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_val32), 1000.0);

        // Test signed
        let i8_val = LeanInt8::mk(lean, -42)?;
        let float_neg = LeanInt8::toFloat(&i8_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_neg), -42.0);

        let i32_val = LeanInt32::mk(lean, -10000)?;
        let float_neg32 = LeanInt32::toFloat(&i32_val, lean)?;
        assert_eq!(LeanFloat::to_f64(&float_neg32), -10000.0);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_log2() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test UInt8
        let u8_1 = LeanUInt8::mk(lean, 1)?;
        assert_eq!(LeanUInt8::log2(&u8_1), 0);

        let u8_8 = LeanUInt8::mk(lean, 8)?;
        assert_eq!(LeanUInt8::log2(&u8_8), 3);

        let u8_16 = LeanUInt8::mk(lean, 16)?;
        assert_eq!(LeanUInt8::log2(&u8_16), 4);

        let u8_15 = LeanUInt8::mk(lean, 15)?;
        assert_eq!(LeanUInt8::log2(&u8_15), 3);

        let u8_0 = LeanUInt8::mk(lean, 0)?;
        assert_eq!(LeanUInt8::log2(&u8_0), 0);

        // Test UInt32
        let u32_1024 = LeanUInt32::mk(lean, 1024)?;
        assert_eq!(LeanUInt32::log2(&u32_1024), 10);

        let u32_1000 = LeanUInt32::mk(lean, 1000)?;
        assert_eq!(LeanUInt32::log2(&u32_1000), 9); // floor(log2(1000)) = 9

        Ok(())
    })
    .unwrap();
}
