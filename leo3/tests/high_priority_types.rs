//! Tests for high-priority types: Float, ByteArray, and UInt types

use leo3::prelude::*;

// ============================================================================
// Float Tests
// ============================================================================

#[test]
fn test_float_creation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let f = LeanFloat::from_f64(lean, std::f64::consts::PI)?;
        assert_eq!(LeanFloat::to_f64(&f), std::f64::consts::PI);

        let zero = LeanFloat::zero(lean)?;
        assert_eq!(LeanFloat::to_f64(&zero), 0.0);

        let one = LeanFloat::one(lean)?;
        assert_eq!(LeanFloat::to_f64(&one), 1.0);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_float_special_values() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let inf = LeanFloat::infinity(lean)?;
        assert!(LeanFloat::isInf(&inf));
        assert!(!LeanFloat::isFinite(&inf));

        let neg_inf = LeanFloat::neg_infinity(lean)?;
        assert!(LeanFloat::isInf(&neg_inf));

        let nan = LeanFloat::nan(lean)?;
        assert!(LeanFloat::isNaN(&nan));
        assert!(!LeanFloat::isFinite(&nan));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_float_arithmetic() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanFloat::from_f64(lean, 10.0)?;
        let b = LeanFloat::from_f64(lean, 3.0)?;

        let sum = LeanFloat::add(lean, &a, &b)?;
        assert_eq!(LeanFloat::to_f64(&sum), 13.0);

        let diff = LeanFloat::sub(lean, &a, &b)?;
        assert_eq!(LeanFloat::to_f64(&diff), 7.0);

        let prod = LeanFloat::mul(lean, &a, &b)?;
        assert_eq!(LeanFloat::to_f64(&prod), 30.0);

        let quot = LeanFloat::div(lean, &a, &b)?;
        assert!((LeanFloat::to_f64(&quot) - 3.333333333).abs() < 0.0001);

        Ok(())
    })
    .expect("test failed");
}

// ============================================================================
// ByteArray Tests
// ============================================================================

#[test]
fn test_bytearray_creation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let ba = LeanByteArray::empty(lean)?;
        assert_eq!(LeanByteArray::size(&ba), 0);
        assert!(LeanByteArray::isEmpty(&ba));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_bytearray_from_bytes() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let ba = LeanByteArray::from_bytes(lean, b"Hello")?;
        assert_eq!(LeanByteArray::size(&ba), 5);
        assert_eq!(LeanByteArray::get(&ba, 0), Some(b'H'));
        assert_eq!(LeanByteArray::get(&ba, 4), Some(b'o'));
        assert_eq!(LeanByteArray::get(&ba, 5), None);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_bytearray_push() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let mut ba = LeanByteArray::empty(lean)?;
        ba = LeanByteArray::push(ba, b'A')?;
        ba = LeanByteArray::push(ba, b'B')?;
        ba = LeanByteArray::push(ba, b'C')?;

        assert_eq!(LeanByteArray::size(&ba), 3);
        assert_eq!(LeanByteArray::to_vec(&ba), vec![b'A', b'B', b'C']);

        Ok(())
    })
    .expect("test failed");
}

// ============================================================================
// UInt Tests
// ============================================================================

#[test]
fn test_uint8() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let u = LeanUInt8::mk(lean, 42)?;
        assert_eq!(LeanUInt8::to_u8(&u), 42);

        let max = LeanUInt8::mk(lean, 255)?;
        assert_eq!(LeanUInt8::to_u8(&max), 255);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_uint16() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let u = LeanUInt16::mk(lean, 1000)?;
        assert_eq!(LeanUInt16::to_u16(&u), 1000);

        let max = LeanUInt16::mk(lean, 65535)?;
        assert_eq!(LeanUInt16::to_u16(&max), 65535);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_uint32() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let u = LeanUInt32::mk(lean, 100000)?;
        assert_eq!(LeanUInt32::to_u32(&u), 100000);

        let max = LeanUInt32::mk(lean, 0xFFFFFFFF)?;
        assert_eq!(LeanUInt32::to_u32(&max), 0xFFFFFFFF);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_uint64() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let u = LeanUInt64::mk(lean, 1000000000)?;
        assert_eq!(LeanUInt64::to_u64(&u), 1000000000);

        let large = LeanUInt64::mk(lean, 0xFFFFFFFFFFFFFFFF)?;
        assert_eq!(LeanUInt64::to_u64(&large), 0xFFFFFFFFFFFFFFFF);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_usize() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let u = LeanUSize::mk(lean, 42)?;
        assert_eq!(LeanUSize::to_usize(&u), 42);

        let large = LeanUSize::mk(lean, usize::MAX)?;
        assert_eq!(LeanUSize::to_usize(&large), usize::MAX);

        Ok(())
    })
    .expect("test failed");
}
