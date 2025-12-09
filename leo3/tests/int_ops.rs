//! Tests for Lean integer operations

use leo3::prelude::*;

#[test]
fn test_int_creation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test positive integers
        let pos = LeanInt::from_i64(lean, 42)?;
        assert_eq!(LeanInt::to_i64(&pos), Some(42));

        // Test negative integers
        let neg = LeanInt::from_i64(lean, -100)?;
        assert_eq!(LeanInt::to_i64(&neg), Some(-100));

        // Test zero
        let zero = LeanInt::zero(lean)?;
        assert_eq!(LeanInt::to_i64(&zero), Some(0));

        // Test one
        let one = LeanInt::one(lean)?;
        assert_eq!(LeanInt::to_i64(&one), Some(1));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_is_non_neg() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let pos = LeanInt::from_i64(lean, 42)?;
        assert!(LeanInt::isNonNeg(&pos));

        let zero = LeanInt::zero(lean)?;
        assert!(LeanInt::isNonNeg(&zero));

        let neg = LeanInt::from_i64(lean, -10)?;
        assert!(!LeanInt::isNonNeg(&neg));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_negation() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let pos = LeanInt::from_i64(lean, 42)?;
        let neg_pos = LeanInt::neg(pos)?;
        assert_eq!(LeanInt::to_i64(&neg_pos), Some(-42));

        let neg = LeanInt::from_i64(lean, -100)?;
        let neg_neg = LeanInt::neg(neg)?;
        assert_eq!(LeanInt::to_i64(&neg_neg), Some(100));

        let zero = LeanInt::zero(lean)?;
        let neg_zero = LeanInt::neg(zero)?;
        assert_eq!(LeanInt::to_i64(&neg_zero), Some(0));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_addition() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 10)?;
        let b = LeanInt::from_i64(lean, 32)?;
        let c = LeanInt::add(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Test with negative numbers
        let x = LeanInt::from_i64(lean, -5)?;
        let y = LeanInt::from_i64(lean, 15)?;
        let z = LeanInt::add(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&z), Some(10));

        // Test negative + negative
        let p = LeanInt::from_i64(lean, -10)?;
        let q = LeanInt::from_i64(lean, -20)?;
        let r = LeanInt::add(&p, &q)?;
        assert_eq!(LeanInt::to_i64(&r), Some(-30));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_subtraction() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 100)?;
        let b = LeanInt::from_i64(lean, 58)?;
        let c = LeanInt::sub(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Test resulting in negative
        let x = LeanInt::from_i64(lean, 10)?;
        let y = LeanInt::from_i64(lean, 25)?;
        let z = LeanInt::sub(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&z), Some(-15));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_multiplication() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 6)?;
        let b = LeanInt::from_i64(lean, 7)?;
        let c = LeanInt::mul(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Test with negative
        let x = LeanInt::from_i64(lean, -3)?;
        let y = LeanInt::from_i64(lean, 4)?;
        let z = LeanInt::mul(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&z), Some(-12));

        // Test negative * negative
        let p = LeanInt::from_i64(lean, -5)?;
        let q = LeanInt::from_i64(lean, -8)?;
        let r = LeanInt::mul(&p, &q)?;
        assert_eq!(LeanInt::to_i64(&r), Some(40));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_division() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 42)?;
        let b = LeanInt::from_i64(lean, 6)?;
        let c = LeanInt::div(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(7));

        // Test truncated division with negative
        let x = LeanInt::from_i64(lean, -17)?;
        let y = LeanInt::from_i64(lean, 5)?;
        let z = LeanInt::div(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&z), Some(-3)); // Truncated toward zero

        // Test division by negative
        let p = LeanInt::from_i64(lean, 17)?;
        let q = LeanInt::from_i64(lean, -5)?;
        let r = LeanInt::div(&p, &q)?;
        assert_eq!(LeanInt::to_i64(&r), Some(-3)); // Truncated toward zero

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_modulus() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 42)?;
        let b = LeanInt::from_i64(lean, 10)?;
        let c = LeanInt::mod_(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(2));

        // Test modulus with negative dividend
        let x = LeanInt::from_i64(lean, -17)?;
        let y = LeanInt::from_i64(lean, 5)?;
        let z = LeanInt::mod_(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&z), Some(-2));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_euclidean_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Euclidean division: always rounds toward negative infinity
        let a = LeanInt::from_i64(lean, 17)?;
        let b = LeanInt::from_i64(lean, 5)?;
        let div = LeanInt::ediv(&a, &b)?;
        let mod_ = LeanInt::emod(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&div), Some(3));
        assert_eq!(LeanInt::to_i64(&mod_), Some(2));

        // Test with negative dividend
        let x = LeanInt::from_i64(lean, -17)?;
        let y = LeanInt::from_i64(lean, 5)?;
        let div2 = LeanInt::ediv(&x, &y)?;
        let mod2 = LeanInt::emod(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&div2), Some(-4)); // Rounds down
        assert_eq!(LeanInt::to_i64(&mod2), Some(3)); // Always non-negative

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_comparisons() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let a = LeanInt::from_i64(lean, 10)?;
        let b = LeanInt::from_i64(lean, 20)?;
        let c = LeanInt::from_i64(lean, 10)?;

        // Test equality
        assert!(LeanInt::eq(&a, &c));
        assert!(!LeanInt::eq(&a, &b));

        // Test less than
        assert!(LeanInt::lt(&a, &b));
        assert!(!LeanInt::lt(&b, &a));
        assert!(!LeanInt::lt(&a, &c));

        // Test less than or equal
        assert!(LeanInt::le(&a, &b));
        assert!(!LeanInt::le(&b, &a));
        assert!(LeanInt::le(&a, &c));

        // Test with negative numbers
        let neg = LeanInt::from_i64(lean, -5)?;
        assert!(LeanInt::lt(&neg, &a));
        assert!(!LeanInt::lt(&a, &neg));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_from_nat() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let nat = LeanNat::from_usize(lean, 42)?;
        let int = LeanInt::ofNat(lean, nat)?;
        assert_eq!(LeanInt::to_i64(&int), Some(42));
        assert!(LeanInt::isNonNeg(&int));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_large_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test numbers that fit in i64
        let large = LeanInt::from_i64(lean, i32::MAX as i64 + 1)?;
        // For large numbers, to_i64 may return None or Some(value) depending on implementation
        // This test just ensures it doesn't panic
        let _ = LeanInt::to_i64(&large);

        let small = LeanInt::from_i64(lean, i32::MIN as i64 - 1)?;
        let _ = LeanInt::to_i64(&small);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_debug_format() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let int = LeanInt::from_i64(lean, 42)?;
        let debug_str = format!("{:?}", int);
        assert!(debug_str.contains("42"));

        let neg_int = LeanInt::from_i64(lean, -100)?;
        let debug_str2 = format!("{:?}", neg_int);
        assert!(debug_str2.contains("-100"));

        Ok(())
    })
    .expect("test failed");
}
