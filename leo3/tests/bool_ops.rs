//! Boolean operation tests for Leo3
//!
//! These tests demonstrate LeanBool functionality including creation,
//! conversion, and logical operations.

use leo3::prelude::*;

#[test]
fn test_bool_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, true)?;

        assert_eq!(LeanBool::toBool(&b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, false)?;

        assert_eq!(LeanBool::toBool(&b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_not_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, true)?;
        let not_b = LeanBool::not(b)?;

        assert_eq!(LeanBool::toBool(&not_b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_not_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, false)?;
        let not_b = LeanBool::not(b)?;

        assert_eq!(LeanBool::toBool(&not_b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_and_true_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, true)?;
        let b = LeanBool::mk(lean, true)?;

        assert_eq!(LeanBool::and(&a, &b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_and_true_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, true)?;
        let b = LeanBool::mk(lean, false)?;

        assert_eq!(LeanBool::and(&a, &b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_and_false_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, false)?;
        let b = LeanBool::mk(lean, true)?;

        assert_eq!(LeanBool::and(&a, &b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_and_false_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, false)?;
        let b = LeanBool::mk(lean, false)?;

        assert_eq!(LeanBool::and(&a, &b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_or_true_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, true)?;
        let b = LeanBool::mk(lean, true)?;

        assert_eq!(LeanBool::or(&a, &b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_or_true_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, true)?;
        let b = LeanBool::mk(lean, false)?;

        assert_eq!(LeanBool::or(&a, &b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_or_false_true() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, false)?;
        let b = LeanBool::mk(lean, true)?;

        assert_eq!(LeanBool::or(&a, &b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_or_false_false() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanBool::mk(lean, false)?;
        let b = LeanBool::mk(lean, false)?;

        assert_eq!(LeanBool::or(&a, &b), false);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_double_negation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, true)?;
        let not_b = LeanBool::not(b)?;
        let not_not_b = LeanBool::not(not_b)?;

        assert_eq!(LeanBool::toBool(&not_not_b), true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_complex_expression() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test: (true && false) || (true && true) = false || true = true
        let t = LeanBool::mk(lean, true)?;
        let f = LeanBool::mk(lean, false)?;
        let t2 = LeanBool::mk(lean, true)?;
        let t3 = LeanBool::mk(lean, true)?;

        let left = LeanBool::and(&t, &f); // false
        let right = LeanBool::and(&t2, &t3); // true

        let left_bool = LeanBool::mk(lean, left)?;
        let right_bool = LeanBool::mk(lean, right)?;

        let result = LeanBool::or(&left_bool, &right_bool);
        assert_eq!(result, true);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_bool_de_morgan_laws() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // De Morgan's Law: !(A && B) = !A || !B
        let a = LeanBool::mk(lean, true)?;
        let b = LeanBool::mk(lean, false)?;

        // Left side: !(A && B)
        let and_result = LeanBool::and(&a, &b); // false
        let and_bool = LeanBool::mk(lean, and_result)?;
        let left = LeanBool::not(and_bool)?; // true

        // Right side: !A || !B
        let not_a = LeanBool::not(a)?; // false
        let not_b = LeanBool::not(b)?; // true
        let right = LeanBool::or(&not_a, &not_b); // true

        assert_eq!(LeanBool::toBool(&left), right);

        Ok(())
    });

    assert!(result.is_ok());
}
