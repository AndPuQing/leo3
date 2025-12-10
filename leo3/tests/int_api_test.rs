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

// ============================================================================
// Arithmetic Operations Tests
// ============================================================================

#[test]
fn test_uint8_arithmetic_basic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Addition
        let a = LeanUInt8::mk(lean, 10)?;
        let b = LeanUInt8::mk(lean, 20)?;
        let result = LeanUInt8::add(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 30);

        // Subtraction
        let a = LeanUInt8::mk(lean, 50)?;
        let b = LeanUInt8::mk(lean, 20)?;
        let result = LeanUInt8::sub(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 30);

        // Multiplication
        let a = LeanUInt8::mk(lean, 5)?;
        let b = LeanUInt8::mk(lean, 6)?;
        let result = LeanUInt8::mul(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 30);

        // Division
        let a = LeanUInt8::mk(lean, 60)?;
        let b = LeanUInt8::mk(lean, 2)?;
        let result = LeanUInt8::div(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 30);

        // Modulo
        let a = LeanUInt8::mk(lean, 17)?;
        let b = LeanUInt8::mk(lean, 5)?;
        let result = LeanUInt8::mod_(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 2);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint8_arithmetic_overflow() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Addition overflow (wrapping)
        let a = LeanUInt8::mk(lean, 250)?;
        let b = LeanUInt8::mk(lean, 10)?;
        let result = LeanUInt8::add(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 4); // 260 wraps to 4

        // Subtraction underflow (wrapping)
        let a = LeanUInt8::mk(lean, 5)?;
        let b = LeanUInt8::mk(lean, 10)?;
        let result = LeanUInt8::sub(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 251); // -5 wraps to 251

        // Multiplication overflow
        let a = LeanUInt8::mk(lean, 200)?;
        let b = LeanUInt8::mk(lean, 2)?;
        let result = LeanUInt8::mul(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 144); // 400 wraps to 144

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint8_division_by_zero() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Division by zero returns 0
        let a = LeanUInt8::mk(lean, 42)?;
        let b = LeanUInt8::mk(lean, 0)?;
        let result = LeanUInt8::div(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0);

        // Modulo by zero returns dividend
        let a = LeanUInt8::mk(lean, 42)?;
        let b = LeanUInt8::mk(lean, 0)?;
        let result = LeanUInt8::mod_(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 42);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint8_negation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Negation (two's complement)
        let a = LeanUInt8::mk(lean, 1)?;
        let result = LeanUInt8::neg(lean, &a)?;
        assert_eq!(LeanUInt8::to_u8(&result), 255); // -1 wraps to 255

        let a = LeanUInt8::mk(lean, 10)?;
        let result = LeanUInt8::neg(lean, &a)?;
        assert_eq!(LeanUInt8::to_u8(&result), 246); // -10 wraps to 246

        let a = LeanUInt8::mk(lean, 0)?;
        let result = LeanUInt8::neg(lean, &a)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0); // -0 = 0

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_arithmetic_basic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Addition
        let a = LeanInt8::mk(lean, 10)?;
        let b = LeanInt8::mk(lean, 20)?;
        let result = LeanInt8::add(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 30);

        // Addition with negatives
        let a = LeanInt8::mk(lean, -10)?;
        let b = LeanInt8::mk(lean, 20)?;
        let result = LeanInt8::add(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 10);

        // Subtraction
        let a = LeanInt8::mk(lean, 50)?;
        let b = LeanInt8::mk(lean, 20)?;
        let result = LeanInt8::sub(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 30);

        // Multiplication
        let a = LeanInt8::mk(lean, -5)?;
        let b = LeanInt8::mk(lean, 6)?;
        let result = LeanInt8::mul(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), -30);

        // Division
        let a = LeanInt8::mk(lean, -60)?;
        let b = LeanInt8::mk(lean, 2)?;
        let result = LeanInt8::div(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), -30);

        // Modulo
        let a = LeanInt8::mk(lean, 17)?;
        let b = LeanInt8::mk(lean, 5)?;
        let result = LeanInt8::mod_(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 2);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_arithmetic_overflow() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Addition overflow (wrapping)
        let a = LeanInt8::mk(lean, 127)?; // MAX
        let b = LeanInt8::mk(lean, 1)?;
        let result = LeanInt8::add(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), -128); // Wraps to MIN

        // Subtraction underflow (wrapping)
        let a = LeanInt8::mk(lean, -128)?; // MIN
        let b = LeanInt8::mk(lean, 1)?;
        let result = LeanInt8::sub(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 127); // Wraps to MAX

        // Multiplication overflow
        let a = LeanInt8::mk(lean, 64)?;
        let b = LeanInt8::mk(lean, 2)?;
        let result = LeanInt8::mul(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), -128); // 128 wraps to -128

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_negation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Negation
        let a = LeanInt8::mk(lean, 42)?;
        let result = LeanInt8::neg(lean, &a)?;
        assert_eq!(LeanInt8::to_i8(&result), -42);

        let a = LeanInt8::mk(lean, -42)?;
        let result = LeanInt8::neg(lean, &a)?;
        assert_eq!(LeanInt8::to_i8(&result), 42);

        // MIN negates to itself (wrapping)
        let a = LeanInt8::mk(lean, -128)?;
        let result = LeanInt8::neg(lean, &a)?;
        assert_eq!(LeanInt8::to_i8(&result), -128);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint32_arithmetic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic operations
        let a = LeanUInt32::mk(lean, 1000)?;
        let b = LeanUInt32::mk(lean, 500)?;

        let result = LeanUInt32::add(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 1500);

        let result = LeanUInt32::sub(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 500);

        let result = LeanUInt32::mul(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 500000);

        let result = LeanUInt32::div(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 2);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int32_arithmetic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic operations with negative numbers
        let a = LeanInt32::mk(lean, -1000)?;
        let b = LeanInt32::mk(lean, 500)?;

        let result = LeanInt32::add(lean, &a, &b)?;
        assert_eq!(LeanInt32::to_i32(&result), -500);

        let result = LeanInt32::sub(lean, &a, &b)?;
        assert_eq!(LeanInt32::to_i32(&result), -1500);

        let result = LeanInt32::mul(lean, &a, &b)?;
        assert_eq!(LeanInt32::to_i32(&result), -500000);

        Ok(())
    })
    .unwrap();
}

// ============================================================================
// Bitwise Operations Tests
// ============================================================================

#[test]
fn test_uint8_bitwise_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // AND operation
        let a = LeanUInt8::mk(lean, 0b11110000)?;
        let b = LeanUInt8::mk(lean, 0b10101010)?;
        let result = LeanUInt8::land(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b10100000);

        // OR operation
        let result = LeanUInt8::lor(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b11111010);

        // XOR operation
        let result = LeanUInt8::xor(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b01011010);

        // Complement operation
        let a = LeanUInt8::mk(lean, 0b10101010)?;
        let result = LeanUInt8::complement(lean, &a)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b01010101);

        // Complement of all 0s is all 1s
        let a = LeanUInt8::mk(lean, 0)?;
        let result = LeanUInt8::complement(lean, &a)?;
        assert_eq!(LeanUInt8::to_u8(&result), 255);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint8_shift_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Left shift
        let a = LeanUInt8::mk(lean, 0b00001111)?;
        let b = LeanUInt8::mk(lean, 2)?;
        let result = LeanUInt8::shiftLeft(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b00111100);

        // Left shift causing overflow
        let a = LeanUInt8::mk(lean, 0b11000000)?;
        let b = LeanUInt8::mk(lean, 2)?;
        let result = LeanUInt8::shiftLeft(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b00000000); // Bits shifted out

        // Right shift (logical for unsigned)
        let a = LeanUInt8::mk(lean, 0b11110000)?;
        let b = LeanUInt8::mk(lean, 2)?;
        let result = LeanUInt8::shiftRight(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b00111100);

        // Shift by 0 should not change value
        let a = LeanUInt8::mk(lean, 0b10101010)?;
        let b = LeanUInt8::mk(lean, 0)?;
        let result = LeanUInt8::shiftLeft(lean, &a, &b)?;
        assert_eq!(LeanUInt8::to_u8(&result), 0b10101010);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_bitwise_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // AND operation
        let a = LeanInt8::mk(lean, 0b01110000)?; // Positive
        let b = LeanInt8::mk(lean, 0b00101010)?; // Positive
        let result = LeanInt8::land(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 0b00100000);

        // OR operation
        let result = LeanInt8::lor(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 0b01111010);

        // XOR operation
        let result = LeanInt8::xor(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 0b01011010);

        // Complement operation on positive number
        let a = LeanInt8::mk(lean, 0)?;
        let result = LeanInt8::complement(lean, &a)?;
        assert_eq!(LeanInt8::to_i8(&result), -1);

        // Complement operation on -1 gives 0
        let a = LeanInt8::mk(lean, -1)?;
        let result = LeanInt8::complement(lean, &a)?;
        assert_eq!(LeanInt8::to_i8(&result), 0);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int8_shift_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Left shift on positive number
        let a = LeanInt8::mk(lean, 0b00001111)?;
        let b = LeanInt8::mk(lean, 2)?;
        let result = LeanInt8::shiftLeft(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 0b00111100);

        // Right shift on positive number (arithmetic shift)
        let a = LeanInt8::mk(lean, 0b01110000)?;
        let b = LeanInt8::mk(lean, 2)?;
        let result = LeanInt8::shiftRight(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), 0b00011100);

        // Right shift on negative number (arithmetic shift preserves sign)
        let a = LeanInt8::mk(lean, -16)?; // 0b11110000 in two's complement
        let b = LeanInt8::mk(lean, 2)?;
        let result = LeanInt8::shiftRight(lean, &a, &b)?;
        assert_eq!(LeanInt8::to_i8(&result), -4); // 0b11111100

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint32_bitwise_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test with larger values
        let a = LeanUInt32::mk(lean, 0xFFFF0000)?;
        let b = LeanUInt32::mk(lean, 0x00FFFF00)?;

        let result = LeanUInt32::land(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 0x00FF0000);

        let result = LeanUInt32::lor(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 0xFFFFFF00);

        let result = LeanUInt32::xor(lean, &a, &b)?;
        assert_eq!(LeanUInt32::to_u32(&result), 0xFF00FF00);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int32_bitwise_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test with negative numbers
        let a = LeanInt32::mk(lean, -1)?; // All bits set
        let b = LeanInt32::mk(lean, 0x00FF00FF)?;

        let result = LeanInt32::land(lean, &a, &b)?;
        assert_eq!(LeanInt32::to_i32(&result), 0x00FF00FF);

        // XOR with -1 is equivalent to complement
        let a = LeanInt32::mk(lean, 0x12345678)?;
        let all_ones = LeanInt32::mk(lean, -1)?;
        let result = LeanInt32::xor(lean, &a, &all_ones)?;
        let complement = LeanInt32::complement(lean, &a)?;
        assert_eq!(LeanInt32::to_i32(&result), LeanInt32::to_i32(&complement));

        Ok(())
    })
    .unwrap();
}

// ============================================================================
// Type Conversion Tests (between different sized types)
// ============================================================================

#[test]
fn test_uint_size_conversions() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // UInt8 -> UInt16
        let u8_val = LeanUInt8::mk(lean, 200)?;
        let u16_val = LeanUInt8::toUInt16(&u8_val, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 200);

        // UInt8 -> UInt32
        let u32_val = LeanUInt8::toUInt32(&u8_val, lean)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 200);

        // UInt8 -> UInt64
        let u64_val = LeanUInt8::toUInt64(&u8_val, lean)?;
        assert_eq!(LeanUInt64::to_u64(&u64_val), 200);

        // UInt16 -> UInt8 (truncation)
        let u16_val = LeanUInt16::mk(lean, 300)?;
        let u8_val = LeanUInt16::toUInt8(&u16_val, lean)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 44); // 300 % 256 = 44

        // UInt16 -> UInt32
        let u16_val = LeanUInt16::mk(lean, 50000)?;
        let u32_val = LeanUInt16::toUInt32(&u16_val, lean)?;
        assert_eq!(LeanUInt32::to_u32(&u32_val), 50000);

        // UInt32 -> UInt16 (truncation)
        let u32_val = LeanUInt32::mk(lean, 70000)?;
        let u16_val = LeanUInt32::toUInt16(&u32_val, lean)?;
        assert_eq!(LeanUInt16::to_u16(&u16_val), 4464); // 70000 % 65536 = 4464

        // UInt32 -> UInt8 (truncation)
        let u32_val = LeanUInt32::mk(lean, 1000)?;
        let u8_val = LeanUInt32::toUInt8(&u32_val, lean)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 232); // 1000 % 256 = 232

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int_size_conversions() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Int8 -> Int16
        let i8_val = LeanInt8::mk(lean, -100)?;
        let i16_val = LeanInt8::toInt16(&i8_val, lean)?;
        assert_eq!(LeanInt16::to_i16(&i16_val), -100);

        // Int8 -> Int32
        let i32_val = LeanInt8::toInt32(&i8_val, lean)?;
        assert_eq!(LeanInt32::to_i32(&i32_val), -100);

        // Int8 -> Int64
        let i64_val = LeanInt8::toInt64(&i8_val, lean)?;
        assert_eq!(LeanInt64::to_i64(&i64_val), -100);

        // Int16 -> Int8 (truncation with wrapping)
        let i16_val = LeanInt16::mk(lean, -200)?;
        let i8_val = LeanInt16::toInt8(&i16_val, lean)?;
        // -200 as i8 wraps
        assert_eq!(LeanInt8::to_i8(&i8_val), 56);

        // Int32 -> Int16 (truncation)
        let i32_val = LeanInt32::mk(lean, -40000)?;
        let i16_val = LeanInt32::toInt16(&i32_val, lean)?;
        // Truncation of lower 16 bits
        let truncated = ((-40000i32) & 0xFFFF) as i16;
        assert_eq!(LeanInt16::to_i16(&i16_val), truncated);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_mixed_sign_conversions() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Unsigned to signed via toInt
        let u8_val = LeanUInt8::mk(lean, 200)?;
        let int_val = LeanUInt8::toInt(&u8_val, lean)?;
        let i8_val = LeanInt8::ofInt(lean, &int_val)?;
        // 200 wraps to -56 when interpreted as signed 8-bit
        assert_eq!(LeanInt8::to_i8(&i8_val), -56);

        // Signed to unsigned via toNat (only works for non-negative)
        let i8_val = LeanInt8::mk(lean, 100)?;
        let nat_val = LeanInt8::toNat(&i8_val, lean)?;
        let u8_val = LeanUInt8::ofNat(lean, &nat_val)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 100);

        // Negative signed to unsigned (via Int, which wraps)
        let i8_neg = LeanInt8::mk(lean, -10)?;
        let int_val = LeanInt8::toInt(&i8_neg, lean)?;
        let u8_val = LeanUInt8::ofInt(lean, &int_val)?;
        assert_eq!(LeanUInt8::to_u8(&u8_val), 246); // -10 wraps to 246

        Ok(())
    })
    .unwrap();
}

// ============================================================================
// Additional Edge Cases for 64-bit types
// ============================================================================

#[test]
fn test_uint64_arithmetic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Large number operations
        let a = LeanUInt64::mk(lean, 10000000000)?;
        let b = LeanUInt64::mk(lean, 5000000000)?;

        let result = LeanUInt64::add(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 15000000000);

        let result = LeanUInt64::sub(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 5000000000);

        // Test multiplication with smaller values to avoid overflow
        let a = LeanUInt64::mk(lean, 1000000)?;
        let b = LeanUInt64::mk(lean, 5000000)?;
        let result = LeanUInt64::mul(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 5000000000000);

        // Test division
        let a = LeanUInt64::mk(lean, 10000000000)?;
        let b = LeanUInt64::mk(lean, 5000000000)?;
        let result = LeanUInt64::div(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 2);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_int64_arithmetic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Large negative number operations
        let a = LeanInt64::mk(lean, -10000000000)?;
        let b = LeanInt64::mk(lean, 5000000000)?;

        let result = LeanInt64::add(lean, &a, &b)?;
        assert_eq!(LeanInt64::to_i64(&result), -5000000000);

        let result = LeanInt64::sub(lean, &a, &b)?;
        assert_eq!(LeanInt64::to_i64(&result), -15000000000);

        // Test multiplication with smaller values to avoid overflow
        let a = LeanInt64::mk(lean, -1000000)?;
        let b = LeanInt64::mk(lean, 5000000)?;
        let result = LeanInt64::mul(lean, &a, &b)?;
        assert_eq!(LeanInt64::to_i64(&result), -5000000000000);

        // Test division
        let a = LeanInt64::mk(lean, -10000000000)?;
        let b = LeanInt64::mk(lean, 5000000000)?;
        let result = LeanInt64::div(lean, &a, &b)?;
        assert_eq!(LeanInt64::to_i64(&result), -2);

        Ok(())
    })
    .unwrap();
}

#[test]
fn test_uint64_bitwise() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanUInt64::mk(lean, 0xFFFFFFFF00000000)?;
        let b = LeanUInt64::mk(lean, 0x00000000FFFFFFFF)?;

        let result = LeanUInt64::land(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 0);

        let result = LeanUInt64::lor(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 0xFFFFFFFFFFFFFFFF);

        let result = LeanUInt64::xor(lean, &a, &b)?;
        assert_eq!(LeanUInt64::to_u64(&result), 0xFFFFFFFFFFFFFFFF);

        Ok(())
    })
    .unwrap();
}
