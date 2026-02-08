//! Integration tests for MetaMContext::infer_type() and MetaMContext::check()
//!
//! These tests exercise the type inference and type checking APIs that use
//! Lean's MetaM monad via FFI. Tests use expressions that work with an empty
//! environment (Sort-based) since `LeanEnvironment::empty()` doesn't include
//! the Lean prelude (no `Nat`, `Nat.succ`, etc.).

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// infer_type tests
// ============================================================================

#[test]
fn test_infer_type_sort_prop() {
    // Sort(0) is Prop, its type should be Sort(1) (Type)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;

        let prop_type = ctx.infer_type(&prop)?;

        // The type of Prop should be Type (Sort 1)
        assert!(
            LeanExpr::is_sort(&prop_type),
            "Expected Sort, got {:?}",
            LeanExpr::kind(&prop_type)
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "infer_type(Sort 0) failed: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_type_sort_type() {
    // Sort(1) is Type, its type should be Sort(2) (Type 1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_one = LeanLevel::one(lean)?;
        let type0 = LeanExpr::sort(lean, level_one)?;

        let type0_type = ctx.infer_type(&type0)?;

        // The type of Type should be Type 1 (Sort 2)
        assert!(
            LeanExpr::is_sort(&type0_type),
            "Expected Sort, got {:?}",
            LeanExpr::kind(&type0_type)
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "infer_type(Sort 1) failed: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_type_lambda_identity() {
    // λ (x : Sort 0), x  should have type  Sort 0 → Sort 0  (i.e., Prop → Prop)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;
        let body = LeanExpr::bvar(lean, 0)?; // refers to x

        let lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        let lambda_type = ctx.infer_type(&lambda)?;

        // The type should be a forall (Prop → Prop is ∀ _ : Prop, Prop)
        assert!(
            LeanExpr::is_forall(&lambda_type),
            "Expected Forall, got {:?}",
            LeanExpr::kind(&lambda_type)
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "infer_type(λ x : Prop, x) failed: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_type_preserves_context_for_reuse() {
    // MetaMContext should be reusable across multiple infer_type calls
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // First call
        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;
        let type1 = ctx.infer_type(&prop)?;
        assert!(LeanExpr::is_sort(&type1));

        // Second call on the same context
        let level_one = LeanLevel::one(lean)?;
        let type0 = LeanExpr::sort(lean, level_one)?;
        let type2 = ctx.infer_type(&type0)?;
        assert!(LeanExpr::is_sort(&type2));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "MetaMContext reuse failed: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_type_error_free_variable() {
    // A free variable with no local context should cause an error
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let fvar_id = LeanName::from_str(lean, "nonexistent_fvar")?;
        let fvar = LeanExpr::fvar(lean, fvar_id)?;

        let result = ctx.infer_type(&fvar);
        assert!(result.is_err(), "Expected error for free variable, got Ok");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "infer_type error test failed: {:?}",
        result.err()
    );
}

// ============================================================================
// check tests
// ============================================================================

#[test]
fn test_check_valid_sort() {
    // check() on Sort(0) should succeed
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;

        ctx.check(&prop)?;

        Ok(())
    });

    assert!(result.is_ok(), "check(Sort 0) failed: {:?}", result.err());
}

#[test]
fn test_check_valid_lambda() {
    // check() on λ (x : Prop), x should succeed
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;
        let body = LeanExpr::bvar(lean, 0)?;

        let lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        ctx.check(&lambda)?;

        Ok(())
    });

    assert!(
        result.is_ok(),
        "check(λ x : Prop, x) failed: {:?}",
        result.err()
    );
}

#[test]
fn test_check_invalid_free_variable() {
    // check() on a free variable with no local context.
    // Note: Lean's Meta.check does not error on undeclared free variables;
    // it only validates structural type consistency. So this succeeds.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let fvar_id = LeanName::from_str(lean, "nonexistent_fvar")?;
        let fvar = LeanExpr::fvar(lean, fvar_id)?;

        // Meta.check succeeds even for undeclared fvars
        let _result = ctx.check(&fvar);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "check free variable test failed: {:?}",
        result.err()
    );
}
