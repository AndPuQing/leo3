//! Natural number operation tests for Leo3
//!
//! These tests demonstrate LeanNat functionality including arithmetic operations,
//! comparisons, and conversions.

use leo3::prelude::*;

#[test]
fn test_nat_creation_and_conversion() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;

        assert_eq!(LeanNat::to_usize(&n)?, 42);
        assert!(LeanNat::is_small(&n));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_zero() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let zero = LeanNat::from_usize(lean, 0)?;

        assert_eq!(LeanNat::to_usize(&zero)?, 0);
        assert!(LeanNat::is_small(&zero));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_addition() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 32)?;
        let sum = LeanNat::add(a, b)?;

        assert_eq!(LeanNat::to_usize(&sum)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_subtraction() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 50)?;
        let b = LeanNat::from_usize(lean, 8)?;
        let diff = LeanNat::sub(a, b)?;

        assert_eq!(LeanNat::to_usize(&diff)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_subtraction_saturating() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Natural number subtraction returns 0 if b > a
        let a = LeanNat::from_usize(lean, 5)?;
        let b = LeanNat::from_usize(lean, 10)?;
        let diff = LeanNat::sub(a, b)?;

        assert_eq!(LeanNat::to_usize(&diff)?, 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_multiplication() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 6)?;
        let b = LeanNat::from_usize(lean, 7)?;
        let product = LeanNat::mul(a, b)?;

        assert_eq!(LeanNat::to_usize(&product)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_division() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 84)?;
        let b = LeanNat::from_usize(lean, 2)?;
        let quotient = LeanNat::div(a, b)?;

        assert_eq!(LeanNat::to_usize(&quotient)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_modulo() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 47)?;
        let b = LeanNat::from_usize(lean, 5)?;
        let remainder = LeanNat::modulo(a, b)?;

        assert_eq!(LeanNat::to_usize(&remainder)?, 2);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_power() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let base = LeanNat::from_usize(lean, 2)?;
        let exp = LeanNat::from_usize(lean, 10)?;
        let result = LeanNat::pow(base, exp)?;

        assert_eq!(LeanNat::to_usize(&result)?, 1024);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_gcd() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 48)?;
        let b = LeanNat::from_usize(lean, 18)?;
        let gcd = LeanNat::gcd(a, b)?;

        assert_eq!(LeanNat::to_usize(&gcd)?, 6);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_equality() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 42)?;
        let b = LeanNat::from_usize(lean, 42)?;
        let c = LeanNat::from_usize(lean, 43)?;

        assert!(LeanNat::eq(&a, &b));
        assert!(!LeanNat::eq(&a, &c));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_less_than() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 42)?;

        assert!(LeanNat::lt(&a, &b));
        assert!(!LeanNat::lt(&b, &a));
        assert!(!LeanNat::lt(&a, &a));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_less_than_or_equal() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 42)?;
        let c = LeanNat::from_usize(lean, 10)?;

        assert!(LeanNat::le(&a, &b));
        assert!(!LeanNat::le(&b, &a));
        assert!(LeanNat::le(&a, &c));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_chained_operations() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Compute (5 + 3) * (10 - 2) = 8 * 8 = 64
        let a = LeanNat::from_usize(lean, 5)?;
        let b = LeanNat::from_usize(lean, 3)?;
        let c = LeanNat::from_usize(lean, 10)?;
        let d = LeanNat::from_usize(lean, 2)?;

        let sum = LeanNat::add(a, b)?;
        let diff = LeanNat::sub(c, d)?;
        let product = LeanNat::mul(sum, diff)?;

        assert_eq!(LeanNat::to_usize(&product)?, 64);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_fibonacci() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Compute first few Fibonacci numbers
        let mut a = LeanNat::from_usize(lean, 0)?;
        let mut b = LeanNat::from_usize(lean, 1)?;

        // Fib(0) = 0, Fib(1) = 1
        assert_eq!(LeanNat::to_usize(&a)?, 0);
        assert_eq!(LeanNat::to_usize(&b)?, 1);

        // Fib(2) = 1
        let c = LeanNat::add(a.clone(), b.clone())?;
        assert_eq!(LeanNat::to_usize(&c)?, 1);

        // Fib(3) = 2
        a = b;
        b = c;
        let c = LeanNat::add(a.clone(), b.clone())?;
        assert_eq!(LeanNat::to_usize(&c)?, 2);

        // Fib(4) = 3
        a = b;
        b = c;
        let c = LeanNat::add(a.clone(), b.clone())?;
        assert_eq!(LeanNat::to_usize(&c)?, 3);

        // Fib(5) = 5
        a = b;
        b = c;
        let c = LeanNat::add(a, b)?;
        assert_eq!(LeanNat::to_usize(&c)?, 5);

        Ok(())
    });

    assert!(result.is_ok());
}
