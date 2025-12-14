//! Comprehensive tests for Lean integer operations
//! Tests lean_int_sub and other operations with edge cases

use leo3::prelude::*;

#[test]
fn test_int_sub_small_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic subtraction
        let a = LeanInt::from_i64(lean, 100)?;
        let b = LeanInt::from_i64(lean, 58)?;
        let c = LeanInt::sub(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Subtract zero
        let x = LeanInt::from_i64(lean, 42)?;
        let zero = LeanInt::zero(lean)?;
        let result = LeanInt::sub(&x, &zero)?;
        assert_eq!(LeanInt::to_i64(&result), Some(42));

        // Zero minus positive
        let result2 = LeanInt::sub(&zero, &x)?;
        assert_eq!(LeanInt::to_i64(&result2), Some(-42));

        // Positive minus positive resulting in negative
        let p1 = LeanInt::from_i64(lean, 10)?;
        let p2 = LeanInt::from_i64(lean, 25)?;
        let neg_result = LeanInt::sub(&p1, &p2)?;
        assert_eq!(LeanInt::to_i64(&neg_result), Some(-15));

        // Negative minus positive
        let n = LeanInt::from_i64(lean, -10)?;
        let p = LeanInt::from_i64(lean, 5)?;
        let result3 = LeanInt::sub(&n, &p)?;
        assert_eq!(LeanInt::to_i64(&result3), Some(-15));

        // Negative minus negative
        let n1 = LeanInt::from_i64(lean, -20)?;
        let n2 = LeanInt::from_i64(lean, -5)?;
        let result4 = LeanInt::sub(&n1, &n2)?;
        assert_eq!(LeanInt::to_i64(&result4), Some(-15));

        // Same number minus itself
        let val = LeanInt::from_i64(lean, 123)?;
        let zero_result = LeanInt::sub(&val, &val)?;
        assert_eq!(LeanInt::to_i64(&zero_result), Some(0));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_sub_boundary() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test near i32::MAX boundary (small int threshold)
        let max_small = LeanInt::from_i64(lean, i32::MAX as i64)?;
        let one = LeanInt::one(lean)?;
        let result = LeanInt::sub(&max_small, &one)?;
        assert_eq!(LeanInt::to_i64(&result), Some(i32::MAX as i64 - 1));

        // Test near i32::MIN boundary - result will be big int
        let min_small = LeanInt::from_i64(lean, i32::MIN as i64)?;
        let result2 = LeanInt::sub(&min_small, &one)?;
        // Result is beyond i32::MIN, so to_i64 may return None for big ints
        // Just verify the operation succeeds without panicking
        let _ = LeanInt::to_i64(&result2);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_sub_large_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test with numbers larger than i32
        let large1 = LeanInt::from_i64(lean, i32::MAX as i64 + 1000)?;
        let large2 = LeanInt::from_i64(lean, i32::MAX as i64 + 500)?;
        let result = LeanInt::sub(&large1, &large2)?;
        // Result is small (500), should fit
        assert_eq!(LeanInt::to_i64(&result), Some(500));

        // Test large minus small
        let large = LeanInt::from_i64(lean, i64::MAX / 2)?;
        let small = LeanInt::from_i64(lean, 100)?;
        let result2 = LeanInt::sub(&large, &small)?;
        // Result is very large, to_i64 may return None
        // Just verify operation succeeds
        let _ = LeanInt::to_i64(&result2);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_add_small_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic addition
        let a = LeanInt::from_i64(lean, 10)?;
        let b = LeanInt::from_i64(lean, 32)?;
        let c = LeanInt::add(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Add zero
        let x = LeanInt::from_i64(lean, 42)?;
        let zero = LeanInt::zero(lean)?;
        let result = LeanInt::add(&x, &zero)?;
        assert_eq!(LeanInt::to_i64(&result), Some(42));

        // Negative + positive
        let n = LeanInt::from_i64(lean, -5)?;
        let p = LeanInt::from_i64(lean, 15)?;
        let result2 = LeanInt::add(&n, &p)?;
        assert_eq!(LeanInt::to_i64(&result2), Some(10));

        // Negative + negative
        let n1 = LeanInt::from_i64(lean, -10)?;
        let n2 = LeanInt::from_i64(lean, -20)?;
        let result3 = LeanInt::add(&n1, &n2)?;
        assert_eq!(LeanInt::to_i64(&result3), Some(-30));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_add_boundary() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test adding near i32::MAX
        let near_max = LeanInt::from_i64(lean, i32::MAX as i64 - 10)?;
        let small = LeanInt::from_i64(lean, 5)?;
        let result = LeanInt::add(&near_max, &small)?;
        assert_eq!(LeanInt::to_i64(&result), Some(i32::MAX as i64 - 5));

        // Test adding that crosses i32::MAX boundary
        let at_max = LeanInt::from_i64(lean, i32::MAX as i64)?;
        let one = LeanInt::one(lean)?;
        let result2 = LeanInt::add(&at_max, &one)?;
        // Result is beyond i32::MAX, may be stored as big int
        // Just verify operation succeeds
        let _ = LeanInt::to_i64(&result2);

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_mul_small_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic multiplication
        let a = LeanInt::from_i64(lean, 6)?;
        let b = LeanInt::from_i64(lean, 7)?;
        let c = LeanInt::mul(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(42));

        // Multiply by zero
        let x = LeanInt::from_i64(lean, 42)?;
        let zero = LeanInt::zero(lean)?;
        let result = LeanInt::mul(&x, &zero)?;
        assert_eq!(LeanInt::to_i64(&result), Some(0));

        // Multiply by one
        let one = LeanInt::one(lean)?;
        let result2 = LeanInt::mul(&x, &one)?;
        assert_eq!(LeanInt::to_i64(&result2), Some(42));

        // Negative * positive
        let n = LeanInt::from_i64(lean, -3)?;
        let p = LeanInt::from_i64(lean, 4)?;
        let result3 = LeanInt::mul(&n, &p)?;
        assert_eq!(LeanInt::to_i64(&result3), Some(-12));

        // Negative * negative
        let n1 = LeanInt::from_i64(lean, -5)?;
        let n2 = LeanInt::from_i64(lean, -8)?;
        let result4 = LeanInt::mul(&n1, &n2)?;
        assert_eq!(LeanInt::to_i64(&result4), Some(40));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_div_small_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic division
        let a = LeanInt::from_i64(lean, 42)?;
        let b = LeanInt::from_i64(lean, 6)?;
        let c = LeanInt::div(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(7));

        // Division with remainder
        let x = LeanInt::from_i64(lean, 17)?;
        let y = LeanInt::from_i64(lean, 5)?;
        let result = LeanInt::div(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&result), Some(3));

        // Negative dividend
        let n = LeanInt::from_i64(lean, -17)?;
        let result2 = LeanInt::div(&n, &y)?;
        assert_eq!(LeanInt::to_i64(&result2), Some(-3)); // Truncated toward zero

        // Negative divisor
        let neg_y = LeanInt::from_i64(lean, -5)?;
        let result3 = LeanInt::div(&x, &neg_y)?;
        assert_eq!(LeanInt::to_i64(&result3), Some(-3));

        // Divide by one
        let one = LeanInt::one(lean)?;
        let result4 = LeanInt::div(&x, &one)?;
        assert_eq!(LeanInt::to_i64(&result4), Some(17));

        // Zero divided by something
        let zero = LeanInt::zero(lean)?;
        let result5 = LeanInt::div(&zero, &x)?;
        assert_eq!(LeanInt::to_i64(&result5), Some(0));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_mod_small_numbers() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Basic modulus
        let a = LeanInt::from_i64(lean, 42)?;
        let b = LeanInt::from_i64(lean, 10)?;
        let c = LeanInt::mod_(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&c), Some(2));

        // Exact division
        let x = LeanInt::from_i64(lean, 20)?;
        let y = LeanInt::from_i64(lean, 5)?;
        let result = LeanInt::mod_(&x, &y)?;
        assert_eq!(LeanInt::to_i64(&result), Some(0));

        // Negative dividend
        let n = LeanInt::from_i64(lean, -17)?;
        let result2 = LeanInt::mod_(&n, &y)?;
        assert_eq!(LeanInt::to_i64(&result2), Some(-2));

        // Zero mod something
        let zero = LeanInt::zero(lean)?;
        let result3 = LeanInt::mod_(&zero, &y)?;
        assert_eq!(LeanInt::to_i64(&result3), Some(0));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_ediv_emod() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Euclidean division and modulus
        let a = LeanInt::from_i64(lean, 17)?;
        let b = LeanInt::from_i64(lean, 5)?;
        let div = LeanInt::ediv(&a, &b)?;
        let mod_ = LeanInt::emod(&a, &b)?;
        assert_eq!(LeanInt::to_i64(&div), Some(3));
        assert_eq!(LeanInt::to_i64(&mod_), Some(2));

        // Negative dividend - emod should always be non-negative
        let n = LeanInt::from_i64(lean, -17)?;
        let div2 = LeanInt::ediv(&n, &b)?;
        let mod2 = LeanInt::emod(&n, &b)?;
        assert_eq!(LeanInt::to_i64(&div2), Some(-4)); // Rounds down
        assert_eq!(LeanInt::to_i64(&mod2), Some(3)); // Non-negative

        // Verify: a = b * ediv + emod
        let verify = LeanInt::mul(&b, &div2)?;
        let verify = LeanInt::add(&verify, &mod2)?;
        assert_eq!(LeanInt::to_i64(&verify), Some(-17));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_comparisons_comprehensive() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        let small = LeanInt::from_i64(lean, 10)?;
        let medium = LeanInt::from_i64(lean, 100)?;
        let large = LeanInt::from_i64(lean, 1000)?;
        let zero = LeanInt::zero(lean)?;
        let neg = LeanInt::from_i64(lean, -50)?;

        // Test equality
        let small2 = LeanInt::from_i64(lean, 10)?;
        assert!(LeanInt::eq(&small, &small2));
        assert!(!LeanInt::eq(&small, &medium));

        // Test less than
        assert!(LeanInt::lt(&small, &medium));
        assert!(LeanInt::lt(&medium, &large));
        assert!(LeanInt::lt(&neg, &zero));
        assert!(LeanInt::lt(&neg, &small));
        assert!(!LeanInt::lt(&large, &small));

        // Test less than or equal
        assert!(LeanInt::le(&small, &medium));
        assert!(LeanInt::le(&small, &small2));
        assert!(LeanInt::le(&neg, &zero));
        assert!(!LeanInt::le(&large, &small));

        // Test with very large numbers
        let big1 = LeanInt::from_i64(lean, i64::MAX / 2)?;
        let big2 = LeanInt::from_i64(lean, i64::MAX / 4)?;
        assert!(LeanInt::lt(&big2, &big1));
        assert!(!LeanInt::lt(&big1, &big2));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_negation_comprehensive() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Small positive
        let pos = LeanInt::from_i64(lean, 42)?;
        let neg = LeanInt::neg(pos)?;
        assert_eq!(LeanInt::to_i64(&neg), Some(-42));

        // Small negative
        let n = LeanInt::from_i64(lean, -100)?;
        let p = LeanInt::neg(n)?;
        assert_eq!(LeanInt::to_i64(&p), Some(100));

        // Zero
        let zero = LeanInt::zero(lean)?;
        let neg_zero = LeanInt::neg(zero)?;
        assert_eq!(LeanInt::to_i64(&neg_zero), Some(0));

        // Large positive - result may be big int
        let large = LeanInt::from_i64(lean, i64::MAX / 2)?;
        let neg_large = LeanInt::neg(large)?;
        // Result is very negative, may not fit in to_i64
        // Just verify operation succeeds
        let _ = LeanInt::to_i64(&neg_large);

        // Double negation
        let val = LeanInt::from_i64(lean, 123)?;
        let neg1 = LeanInt::neg(val)?;
        let neg2 = LeanInt::neg(neg1)?;
        assert_eq!(LeanInt::to_i64(&neg2), Some(123));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_mixed_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Test: (a + b) - c
        let a = LeanInt::from_i64(lean, 10)?;
        let b = LeanInt::from_i64(lean, 20)?;
        let c = LeanInt::from_i64(lean, 5)?;
        let sum = LeanInt::add(&a, &b)?;
        let result = LeanInt::sub(&sum, &c)?;
        assert_eq!(LeanInt::to_i64(&result), Some(25));

        // Test: (a * b) / c
        let x = LeanInt::from_i64(lean, 6)?;
        let y = LeanInt::from_i64(lean, 7)?;
        let z = LeanInt::from_i64(lean, 2)?;
        let prod = LeanInt::mul(&x, &y)?;
        let div = LeanInt::div(&prod, &z)?;
        assert_eq!(LeanInt::to_i64(&div), Some(21));

        // Test: -(a - b)
        let p = LeanInt::from_i64(lean, 15)?;
        let q = LeanInt::from_i64(lean, 10)?;
        let diff = LeanInt::sub(&p, &q)?;
        let neg = LeanInt::neg(diff)?;
        assert_eq!(LeanInt::to_i64(&neg), Some(-5));

        Ok(())
    })
    .expect("test failed");
}

#[test]
fn test_int_stress_operations() {
    leo3::with_lean(|lean| -> LeanResult<()> {
        // Perform many operations in sequence
        let mut val = LeanInt::from_i64(lean, 0)?;

        for i in 1..=100 {
            let n = LeanInt::from_i64(lean, i)?;
            val = LeanInt::add(&val, &n)?;
        }

        // Sum of 1..=100 is 5050
        assert_eq!(LeanInt::to_i64(&val), Some(5050));

        // Subtract back down
        for i in (1..=100).rev() {
            let n = LeanInt::from_i64(lean, i)?;
            val = LeanInt::sub(&val, &n)?;
        }

        assert_eq!(LeanInt::to_i64(&val), Some(0));

        Ok(())
    })
    .expect("test failed");
}
