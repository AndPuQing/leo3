//! Integration tests for MetaMContext::is_def_eq()

use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_is_def_eq_same_sort() {
    // Sort(0) should be definitionally equal to Sort(0)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero1 = LeanLevel::zero(lean)?;
        let prop1 = LeanExpr::sort(lean, level_zero1)?;
        let level_zero2 = LeanLevel::zero(lean)?;
        let prop2 = LeanExpr::sort(lean, level_zero2)?;

        let eq = ctx.is_def_eq(&prop1, &prop2)?;
        assert!(eq, "Sort(0) should be def-eq to Sort(0)");

        Ok(())
    });

    assert!(result.is_ok(), "is_def_eq test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_different_sorts() {
    // Sort(0) should NOT be definitionally equal to Sort(1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero = LeanLevel::zero(lean)?;
        let level_one = LeanLevel::one(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;
        let type0 = LeanExpr::sort(lean, level_one)?;

        let eq = ctx.is_def_eq(&prop, &type0)?;
        assert!(!eq, "Sort(0) should NOT be def-eq to Sort(1)");

        Ok(())
    });

    assert!(result.is_ok(), "is_def_eq test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_alpha_equivalent_lambdas() {
    // λ (x : Prop), x  should be def-eq to  λ (y : Prop), y
    // (alpha-equivalent)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero1 = LeanLevel::zero(lean)?;
        let prop1 = LeanExpr::sort(lean, level_zero1)?;
        let body1 = LeanExpr::bvar(lean, 0)?;
        let x_name = LeanName::from_str(lean, "x")?;
        let lambda_x = LeanExpr::lambda(x_name, prop1, body1, BinderInfo::Default)?;

        let level_zero2 = LeanLevel::zero(lean)?;
        let prop2 = LeanExpr::sort(lean, level_zero2)?;
        let body2 = LeanExpr::bvar(lean, 0)?;
        let y_name = LeanName::from_str(lean, "y")?;
        let lambda_y = LeanExpr::lambda(y_name, prop2, body2, BinderInfo::Default)?;

        let eq = ctx.is_def_eq(&lambda_x, &lambda_y)?;
        assert!(eq, "Alpha-equivalent lambdas should be def-eq");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "is_def_eq alpha test failed: {:?}",
        result.err()
    );
}

#[test]
fn test_is_def_eq_preserves_context() {
    // MetaMContext should be reusable after is_def_eq calls
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero1 = LeanLevel::zero(lean)?;
        let prop1 = LeanExpr::sort(lean, level_zero1)?;
        let level_zero2 = LeanLevel::zero(lean)?;
        let prop2 = LeanExpr::sort(lean, level_zero2)?;

        // First call
        let eq1 = ctx.is_def_eq(&prop1, &prop2)?;
        assert!(eq1);

        // Second call on same context
        let level_one1 = LeanLevel::one(lean)?;
        let type1 = LeanExpr::sort(lean, level_one1)?;
        let level_one2 = LeanLevel::one(lean)?;
        let type2 = LeanExpr::sort(lean, level_one2)?;
        let eq2 = ctx.is_def_eq(&type1, &type2)?;
        assert!(eq2);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "is_def_eq context reuse failed: {:?}",
        result.err()
    );
}
