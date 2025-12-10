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
        let remainder = LeanNat::mod_(a, b)?;

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

        assert!(LeanNat::decEq(&a, &b));
        assert!(!LeanNat::decEq(&a, &c));

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

        assert!(LeanNat::decLt(&a, &b));
        assert!(!LeanNat::decLt(&b, &a));
        assert!(!LeanNat::decLt(&a, &a));

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

        assert!(LeanNat::decLe(&a, &b));
        assert!(!LeanNat::decLe(&b, &a));
        assert!(LeanNat::decLe(&a, &c));

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

#[test]
fn test_nat_pred() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        let pred = LeanNat::pred(n)?;
        assert_eq!(LeanNat::to_usize(&pred)?, 41);

        // pred of 0 should be 0
        let zero = LeanNat::from_usize(lean, 0)?;
        let pred_zero = LeanNat::pred(zero)?;
        assert_eq!(LeanNat::to_usize(&pred_zero)?, 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_log2() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 1024)?;
        let log = LeanNat::log2(&n)?;
        assert_eq!(LeanNat::to_usize(&log)?, 10);

        let n2 = LeanNat::from_usize(lean, 8)?;
        let log2 = LeanNat::log2(&n2)?;
        assert_eq!(LeanNat::to_usize(&log2)?, 3);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_bitwise_and() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 5)?; // 0b0101
        let b = LeanNat::from_usize(lean, 3)?; // 0b0011
        let result = LeanNat::land(a, b)?;
        assert_eq!(LeanNat::to_usize(&result)?, 1); // 0b0001

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_bitwise_or() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 5)?; // 0b0101
        let b = LeanNat::from_usize(lean, 3)?; // 0b0011
        let result = LeanNat::lor(a, b)?;
        assert_eq!(LeanNat::to_usize(&result)?, 7); // 0b0111

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_bitwise_xor() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 5)?; // 0b0101
        let b = LeanNat::from_usize(lean, 3)?; // 0b0011
        let result = LeanNat::xor(a, b)?;
        assert_eq!(LeanNat::to_usize(&result)?, 6); // 0b0110

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_shift_left() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 5)?;
        let shift = LeanNat::from_usize(lean, 2)?;
        let result = LeanNat::shiftLeft(n, shift)?;
        assert_eq!(LeanNat::to_usize(&result)?, 20);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_shift_right() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 20)?;
        let shift = LeanNat::from_usize(lean, 2)?;
        let result = LeanNat::shiftRight(n, shift)?;
        assert_eq!(LeanNat::to_usize(&result)?, 5);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_test_bit() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 5)?; // 0b0101
        let idx0 = LeanNat::from_usize(lean, 0)?;
        let idx1 = LeanNat::from_usize(lean, 1)?;
        let idx2 = LeanNat::from_usize(lean, 2)?;

        assert!(LeanNat::testBit(&n, &idx0)); // bit 0 is 1
        assert!(!LeanNat::testBit(&n, &idx1)); // bit 1 is 0
        assert!(LeanNat::testBit(&n, &idx2)); // bit 2 is 1

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_min_max() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 42)?;

        let min = LeanNat::min(&a, &b)?;
        assert_eq!(LeanNat::to_usize(&min)?, 10);

        let max = LeanNat::max(&a, &b)?;
        assert_eq!(LeanNat::to_usize(&max)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_lcm() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 12)?;
        let b = LeanNat::from_usize(lean, 18)?;
        let lcm = LeanNat::lcm(a, b)?;
        assert_eq!(LeanNat::to_usize(&lcm)?, 36);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_boolean_comparisons() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 42)?;
        let c = LeanNat::from_usize(lean, 10)?;

        // beq
        assert!(LeanNat::beq(&a, &c));
        assert!(!LeanNat::beq(&a, &b));

        // blt
        assert!(LeanNat::blt(&a, &b));
        assert!(!LeanNat::blt(&b, &a));
        assert!(!LeanNat::blt(&a, &c));

        // ble
        assert!(LeanNat::ble(&a, &b));
        assert!(!LeanNat::ble(&b, &a));
        assert!(LeanNat::ble(&a, &c));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_conversions() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;

        assert_eq!(LeanNat::toUInt8(&n)?, 42u8);
        assert_eq!(LeanNat::toUInt16(&n)?, 42u16);
        assert_eq!(LeanNat::toUInt32(&n)?, 42u32);
        assert_eq!(LeanNat::toUInt64(&n)?, 42u64);
        assert_eq!(LeanNat::toUSize(&n)?, 42usize);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_is_power_of_two() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let pow2_1 = LeanNat::from_usize(lean, 1)?;
        let pow2_2 = LeanNat::from_usize(lean, 2)?;
        let pow2_8 = LeanNat::from_usize(lean, 8)?;
        let pow2_16 = LeanNat::from_usize(lean, 16)?;
        let not_pow2 = LeanNat::from_usize(lean, 5)?;
        let zero = LeanNat::from_usize(lean, 0)?;

        assert!(LeanNat::isPowerOfTwo(&pow2_1));
        assert!(LeanNat::isPowerOfTwo(&pow2_2));
        assert!(LeanNat::isPowerOfTwo(&pow2_8));
        assert!(LeanNat::isPowerOfTwo(&pow2_16));
        assert!(!LeanNat::isPowerOfTwo(&not_pow2));
        assert!(!LeanNat::isPowerOfTwo(&zero));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nat_next_power_of_two() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n1 = LeanNat::from_usize(lean, 5)?;
        let next1 = LeanNat::nextPowerOfTwo(n1)?;
        assert_eq!(LeanNat::to_usize(&next1)?, 8);

        let n2 = LeanNat::from_usize(lean, 8)?;
        let next2 = LeanNat::nextPowerOfTwo(n2)?;
        assert_eq!(LeanNat::to_usize(&next2)?, 8);

        let n3 = LeanNat::from_usize(lean, 17)?;
        let next3 = LeanNat::nextPowerOfTwo(n3)?;
        assert_eq!(LeanNat::to_usize(&next3)?, 32);

        Ok(())
    });

    assert!(result.is_ok());
}
