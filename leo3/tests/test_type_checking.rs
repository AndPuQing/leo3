//! Comprehensive type checking tests (Issue #39)
//!
//! Tests covering type inference, type checking, whnf, and isDefEq across
//! a variety of expression types. All tests use an empty environment (no prelude)
//! so only Sort-based expressions are available.

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// Type Inference — forall expressions
// ============================================================================

#[test]
fn test_infer_type_forall_prop_to_prop() {
    // ∀ (x : Prop), Prop  should have type  Sort(1)
    // In Lean: the type of a forall is determined by imax of domain/codomain levels
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let forall_expr = LeanExpr::forall(x_name, prop, body, BinderInfo::Default)?;

        let ty = ctx.infer_type(&forall_expr)?;
        assert!(
            LeanExpr::is_sort(&ty),
            "Type of (∀ x : Prop, Prop) should be a Sort, got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_infer_type_forall_type_to_type() {
    // ∀ (A : Type), Type  should have type  Sort(2) (Type 1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let a_name = LeanName::from_str(lean, "A")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let body = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let forall_expr = LeanExpr::forall(a_name, type0, body, BinderInfo::Default)?;

        let ty = ctx.infer_type(&forall_expr)?;
        assert!(LeanExpr::is_sort(&ty));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Type Inference — let expressions
// ============================================================================

#[test]
fn test_infer_type_let_simple() {
    // let x : Prop := Prop in x  should have type Prop (Sort 0)
    // Actually: let x : Sort(1) := Sort(0) in bvar(0)
    // The type of the body (bvar 0) is the type annotation Sort(1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let type1 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?; // Type
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?; // Prop
        let body = LeanExpr::bvar(lean, 0)?; // refers to x
        let let_expr = LeanExpr::let_(x_name, type1, prop, body, false)?;

        let ty = ctx.infer_type(&let_expr)?;
        assert!(
            LeanExpr::is_sort(&ty),
            "Type of (let x : Type := Prop in x) should be Sort, got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_infer_type_let_nested() {
    // let x : Type := Prop in let y : Type := x in y
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let y_name = LeanName::from_str(lean, "y")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Inner let: let y : Type := bvar(0) in bvar(0)
        // bvar(0) in value refers to x, bvar(0) in body refers to y
        let inner_type = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let inner_value = LeanExpr::bvar(lean, 0)?; // x
        let inner_body = LeanExpr::bvar(lean, 0)?; // y
        let inner_let = LeanExpr::let_(y_name, inner_type, inner_value, inner_body, false)?;

        let outer_let = LeanExpr::let_(x_name, type0, prop, inner_let, false)?;

        let ty = ctx.infer_type(&outer_let)?;
        assert!(
            LeanExpr::is_sort(&ty),
            "Type of nested let should be Sort, got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Type Inference — nested applications
// ============================================================================

#[test]
fn test_infer_type_nested_application() {
    // (λ (f : Prop → Prop), λ (x : Prop), f x) applied to (λ (y : Prop), y)
    // should have type Prop → Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop_to_prop = LeanExpr::arrow(prop, prop2)?;

        // λ (f : Prop → Prop), λ (x : Prop), f x
        let f_name = LeanName::from_str(lean, "f")?;
        let x_name = LeanName::from_str(lean, "x")?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let f_var = LeanExpr::bvar(lean, 1)?; // f (outer binder)
        let x_var = LeanExpr::bvar(lean, 0)?; // x (inner binder)
        let f_x = LeanExpr::app(&f_var, &x_var)?;
        let inner_lambda = LeanExpr::lambda(x_name, prop3, f_x, BinderInfo::Default)?;
        let outer_lambda =
            LeanExpr::lambda(f_name, prop_to_prop, inner_lambda, BinderInfo::Default)?;

        // Identity: λ (y : Prop), y
        let y_name = LeanName::from_str(lean, "y")?;
        let prop4 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let y_body = LeanExpr::bvar(lean, 0)?;
        let identity = LeanExpr::lambda(y_name, prop4, y_body, BinderInfo::Default)?;

        // Apply outer_lambda to identity
        let applied = LeanExpr::app(&outer_lambda, &identity)?;

        let ty = ctx.infer_type(&applied)?;
        // Result should be Prop → Prop (a forall/arrow type)
        assert!(
            LeanExpr::is_forall(&ty),
            "Type of applied expression should be Forall, got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Type Inference — universe polymorphism
// ============================================================================

#[test]
fn test_infer_type_universe_polymorphism() {
    // Sort(u+1) should have type Sort(u+2)
    // Using level succ to create higher universes
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
        let sort2 = LeanExpr::sort(lean, level2)?;

        let ty = ctx.infer_type(&sort2)?;
        assert!(
            LeanExpr::is_sort(&ty),
            "Type of Sort(2) should be Sort(3), got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_infer_type_max_universe() {
    // Sort(max 0 1) should have type Sort(max 0 1 + 1) = Sort(2)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let max_level = LeanLevel::max(LeanLevel::zero(lean)?, LeanLevel::one(lean)?)?;
        let sort_max = LeanExpr::sort(lean, max_level)?;

        let ty = ctx.infer_type(&sort_max)?;
        assert!(LeanExpr::is_sort(&ty));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Type Checking — dependent function types
// ============================================================================

#[test]
fn test_check_dependent_function_type() {
    // ∀ (A : Type), A → A  should be type-correct
    // In de Bruijn: ∀ (A : Sort 1), ∀ (_ : bvar(0)), bvar(1)
    // arrow(bvar(0), bvar(0)) gives ∀ (_ : bvar(0)), bvar(0) which is wrong —
    // the codomain bvar(0) refers to _ not A. We need bvar(1) for the codomain.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let a_name = LeanName::from_str(lean, "A")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        // Body: ∀ (_ : bvar(0)), bvar(1)  i.e. A → A
        let underscore = LeanName::from_str(lean, "_")?;
        let domain = LeanExpr::bvar(lean, 0)?; // A
        let codomain = LeanExpr::bvar(lean, 1)?; // A (shifted by the inner forall binder)
        let a_to_a = LeanExpr::forall(underscore, domain, codomain, BinderInfo::Default)?;
        let forall_expr = LeanExpr::forall(a_name, type0, a_to_a, BinderInfo::Default)?;

        ctx.check(&forall_expr)?;

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_check_universe_level_consistency() {
    // Sort(0) : Sort(1) : Sort(2) — each level is consistent
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        ctx.check(&prop)?;

        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        ctx.check(&type0)?;

        let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
        let type1 = LeanExpr::sort(lean, level2)?;
        ctx.check(&type1)?;

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_check_application_wrong_argument_type() {
    // (λ (x : Type), x) applied to a lambda (which is not a Type) should fail
    // λ (x : Type), x  expects a Type, but we pass  λ (y : Prop), y  which has type Prop → Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // λ (x : Sort 2), x  — expects something of type Type 1 (Sort 2)
        let x_name = LeanName::from_str(lean, "x")?;
        let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
        let sort2 = LeanExpr::sort(lean, level2)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, sort2, body, BinderInfo::Default)?;

        // Apply to Sort(0) which has type Sort(1), not Sort(2)
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bad_app = LeanExpr::app(&lambda, &prop)?;

        // check() should fail because Sort(0) : Sort(1) but we need Sort(2)
        let check_result = ctx.check(&bad_app);
        assert!(
            check_result.is_err(),
            "Applying (λ x : Sort 2, x) to Sort 0 should fail type check"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_check_lambda_correct_annotation() {
    // λ (x : Prop), x  with correct annotation should pass
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        ctx.check(&lambda)?;

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Weak Head Normal Form
// ============================================================================

#[test]
fn test_whnf_already_normal_sort() {
    // Sort is already in whnf
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let whnf = ctx.whnf(&prop)?;
        assert!(LeanExpr::is_sort(&whnf));
        assert!(LeanExpr::alpha_eqv(&prop, &whnf));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_whnf_already_normal_lambda() {
    // Lambda is already in whnf (lambdas are values)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        let whnf = ctx.whnf(&lambda)?;
        assert!(LeanExpr::is_lambda(&whnf));
        assert!(LeanExpr::alpha_eqv(&lambda, &whnf));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_whnf_already_normal_forall() {
    // Forall is already in whnf
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let forall_expr = LeanExpr::forall(x_name, prop, body, BinderInfo::Default)?;

        let whnf = ctx.whnf(&forall_expr)?;
        assert!(LeanExpr::is_forall(&whnf));
        assert!(LeanExpr::alpha_eqv(&forall_expr, &whnf));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when whnf performs actual reduction (FFI refcount bug)"]
fn test_whnf_let_substitution() {
    // whnf of (let x : Type := Prop in x) should reduce to Prop (Sort 0)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let let_expr = LeanExpr::let_(x_name, type0, prop, body, false)?;

        let whnf = ctx.whnf(&let_expr)?;
        // After whnf, the let should be substituted: x becomes Prop
        assert!(
            LeanExpr::is_sort(&whnf),
            "whnf of (let x := Prop in x) should be Sort, got {:?}",
            LeanExpr::kind(&whnf)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when whnf performs actual reduction (FFI refcount bug)"]
fn test_whnf_beta_reduction() {
    // whnf of (λ x : Prop, x) Prop  should reduce to Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        let arg = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let app = LeanExpr::app(&lambda, &arg)?;

        let whnf = ctx.whnf(&app)?;
        assert!(
            LeanExpr::is_sort(&whnf),
            "whnf of ((λ x : Prop, x) Prop) should be Sort, got {:?}",
            LeanExpr::kind(&whnf)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when whnf performs actual reduction (FFI refcount bug)"]
fn test_whnf_context_reuse() {
    // Multiple whnf calls on the same context should work
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // First: whnf of Sort(0)
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let r1 = ctx.whnf(&prop)?;
        assert!(LeanExpr::is_sort(&r1));

        // Second: whnf of a let expression
        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let let_expr = LeanExpr::let_(x_name, type0, prop2, body, false)?;
        let r2 = ctx.whnf(&let_expr)?;
        assert!(LeanExpr::is_sort(&r2));

        // Third: whnf of a lambda (should stay lambda)
        let y_name = LeanName::from_str(lean, "y")?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body3 = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(y_name, prop3, body3, BinderInfo::Default)?;
        let r3 = ctx.whnf(&lambda)?;
        assert!(LeanExpr::is_lambda(&r3));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Definitional Equality
// ============================================================================

#[test]
fn test_is_def_eq_same_expression() {
    // Any expression should be def-eq to itself
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(ctx.is_def_eq(&prop, &prop)?);

        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        assert!(ctx.is_def_eq(&type0, &type0)?);

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_alpha_equivalent() {
    // λ (x : Prop), x  should be def-eq to  λ (y : Prop), y
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body1 = LeanExpr::bvar(lean, 0)?;
        let lambda_x = LeanExpr::lambda(x_name, prop1, body1, BinderInfo::Default)?;

        let y_name = LeanName::from_str(lean, "y")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body2 = LeanExpr::bvar(lean, 0)?;
        let lambda_y = LeanExpr::lambda(y_name, prop2, body2, BinderInfo::Default)?;

        assert!(
            ctx.is_def_eq(&lambda_x, &lambda_y)?,
            "Alpha-equivalent lambdas should be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when is_def_eq performs reduction (FFI refcount bug)"]
fn test_is_def_eq_beta_reduced() {
    // (λ x : Prop, x) Prop  should be def-eq to  Prop
    // Beta-reduced vs unreduced forms
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Unreduced: (λ x : Prop, x) Prop
        let x_name = LeanName::from_str(lean, "x")?;
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop1, body, BinderInfo::Default)?;
        let arg = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let unreduced = LeanExpr::app(&lambda, &arg)?;

        // Reduced: Prop
        let reduced = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        assert!(
            ctx.is_def_eq(&unreduced, &reduced)?,
            "Beta-reduced and unreduced forms should be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_different_types_not_equal() {
    // Prop (Sort 0) should NOT be def-eq to Type (Sort 1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;

        assert!(
            !ctx.is_def_eq(&prop, &type0)?,
            "Prop and Type should NOT be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_different_lambdas_not_equal() {
    // λ (x : Prop), x  should NOT be def-eq to  λ (x : Type), x
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name1 = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body1 = LeanExpr::bvar(lean, 0)?;
        let lambda_prop = LeanExpr::lambda(x_name1, prop, body1, BinderInfo::Default)?;

        let x_name2 = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let body2 = LeanExpr::bvar(lean, 0)?;
        let lambda_type = LeanExpr::lambda(x_name2, type0, body2, BinderInfo::Default)?;

        assert!(
            !ctx.is_def_eq(&lambda_prop, &lambda_type)?,
            "Lambdas with different binder types should NOT be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when is_def_eq performs reduction (FFI refcount bug)"]
fn test_is_def_eq_let_reduces() {
    // (let x : Type := Prop in x) should be def-eq to Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop_val = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let let_expr = LeanExpr::let_(x_name, type0, prop_val, body, false)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        assert!(
            ctx.is_def_eq(&let_expr, &prop)?,
            "(let x := Prop in x) should be def-eq to Prop"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_empty_environment_operations() {
    // All operations should work on an empty environment
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // infer_type
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let ty = ctx.infer_type(&prop)?;
        assert!(LeanExpr::is_sort(&ty));

        // whnf
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let whnf = ctx.whnf(&prop2)?;
        assert!(LeanExpr::is_sort(&whnf));

        // is_def_eq
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop4 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(ctx.is_def_eq(&prop3, &prop4)?);

        // check
        let prop5 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        ctx.check(&prop5)?;

        // is_type_correct
        let prop6 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(ctx.is_type_correct(&prop6));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_deeply_nested_expressions() {
    // Build a deeply nested lambda: λ x₁ : Prop, λ x₂ : Prop, ... λ xₙ : Prop, x₁
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let depth = 20;
        // Body refers to the outermost binder (de Bruijn index = depth - 1)
        let mut expr = LeanExpr::bvar(lean, depth - 1)?;

        for i in (0..depth).rev() {
            let name = LeanName::from_str(lean, &format!("x{}", i))?;
            let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            expr = LeanExpr::lambda(name, prop, expr, BinderInfo::Default)?;
        }

        // Should be type-correct
        assert!(ctx.is_type_correct(&expr));

        // Should be able to infer type
        let ty = ctx.infer_type(&expr)?;
        assert!(LeanExpr::is_forall(&ty));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_multiple_sequential_operations() {
    // Run many operations sequentially on the same context
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        for i in 0..10 {
            // Create Sort(i)
            let mut level = LeanLevel::zero(lean)?;
            for _ in 0..i {
                level = LeanLevel::succ(level)?;
            }
            let sort = LeanExpr::sort(lean, level)?;

            // infer_type
            let ty = ctx.infer_type(&sort)?;
            assert!(LeanExpr::is_sort(&ty));

            // whnf
            let whnf = ctx.whnf(&sort)?;
            assert!(LeanExpr::is_sort(&whnf));

            // is_def_eq with itself
            assert!(ctx.is_def_eq(&sort, &sort)?);

            // check
            ctx.check(&sort)?;
        }

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_infer_type_arrow_chain() {
    // Prop → Prop → Prop  should have type Sort(1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let inner_arrow = LeanExpr::arrow(prop2, prop3)?;
        let outer_arrow = LeanExpr::arrow(prop1, inner_arrow)?;

        let ty = ctx.infer_type(&outer_arrow)?;
        assert!(
            LeanExpr::is_sort(&ty),
            "Type of (Prop → Prop → Prop) should be Sort, got {:?}",
            LeanExpr::kind(&ty)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_is_def_eq_forall_alpha_equivalent() {
    // ∀ (a : Prop), a  should be def-eq to  ∀ (b : Prop), b
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let a_name = LeanName::from_str(lean, "a")?;
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body1 = LeanExpr::bvar(lean, 0)?;
        let forall_a = LeanExpr::forall(a_name, prop1, body1, BinderInfo::Default)?;

        let b_name = LeanName::from_str(lean, "b")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body2 = LeanExpr::bvar(lean, 0)?;
        let forall_b = LeanExpr::forall(b_name, prop2, body2, BinderInfo::Default)?;

        assert!(
            ctx.is_def_eq(&forall_a, &forall_b)?,
            "Alpha-equivalent foralls should be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when whnf performs actual reduction (FFI refcount bug)"]
fn test_whnf_nested_let() {
    // let x : Type := Prop in let y : Type := x in y
    // Should reduce to Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let y_name = LeanName::from_str(lean, "y")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let inner_type = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let inner_value = LeanExpr::bvar(lean, 0)?; // x
        let inner_body = LeanExpr::bvar(lean, 0)?; // y
        let inner_let = LeanExpr::let_(y_name, inner_type, inner_value, inner_body, false)?;

        let outer_let = LeanExpr::let_(x_name, type0, prop, inner_let, false)?;

        let whnf = ctx.whnf(&outer_let)?;
        assert!(
            LeanExpr::is_sort(&whnf),
            "whnf of nested let should reduce to Sort, got {:?}",
            LeanExpr::kind(&whnf)
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
fn test_check_polymorphic_identity() {
    // λ (A : Type), λ (x : A), x  should be type-correct
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let a_name = LeanName::from_str(lean, "A")?;
        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let x_body = LeanExpr::bvar(lean, 0)?; // x

        // Inner: λ (x : A), x  where A is bvar(1) from outer
        let a_ref_inner = LeanExpr::bvar(lean, 1)?;
        let inner = LeanExpr::lambda(x_name, a_ref_inner, x_body, BinderInfo::Default)?;

        // Outer: λ (A : Type), inner
        let poly_id = LeanExpr::lambda(a_name, type0, inner, BinderInfo::Default)?;

        // Type should be ∀ (A : Type), A → A
        let ty = ctx.infer_type(&poly_id)?;
        assert!(LeanExpr::is_forall(&ty));

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when is_def_eq performs reduction (FFI refcount bug)"]
fn test_is_def_eq_eta_expansion() {
    // λ (x : Prop), (λ (y : Prop), y) x  should be def-eq to  λ (x : Prop), x
    // This tests eta/beta equivalence
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Simple identity: λ (x : Prop), x
        let x_name = LeanName::from_str(lean, "x")?;
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body1 = LeanExpr::bvar(lean, 0)?;
        let simple_id = LeanExpr::lambda(x_name, prop1, body1, BinderInfo::Default)?;

        // Expanded: λ (x : Prop), (λ (y : Prop), y) x
        let x_name2 = LeanName::from_str(lean, "x")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let y_name = LeanName::from_str(lean, "y")?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let y_body = LeanExpr::bvar(lean, 0)?;
        let inner_id = LeanExpr::lambda(y_name, prop3, y_body, BinderInfo::Default)?;
        let x_ref = LeanExpr::bvar(lean, 0)?;
        let app_body = LeanExpr::app(&inner_id, &x_ref)?;
        let expanded = LeanExpr::lambda(x_name2, prop2, app_body, BinderInfo::Default)?;

        assert!(
            ctx.is_def_eq(&simple_id, &expanded)?,
            "Beta-equivalent lambdas should be def-eq"
        );

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[ignore = "SIGSEGV during cleanup when whnf performs actual reduction (FFI refcount bug)"]
fn test_mixed_operations_on_same_context() {
    // Interleave different operations to test context stability
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // 1. infer_type
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let ty = ctx.infer_type(&prop)?;
        assert!(LeanExpr::is_sort(&ty));

        // 2. is_def_eq
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(ctx.is_def_eq(&prop2, &prop3)?);

        // 3. whnf
        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop4 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let let_expr = LeanExpr::let_(x_name, type0, prop4, body, false)?;
        let whnf = ctx.whnf(&let_expr)?;
        assert!(LeanExpr::is_sort(&whnf));

        // 4. check
        let prop5 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        ctx.check(&prop5)?;

        // 5. infer_type again (context should still work)
        let type1 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let ty2 = ctx.infer_type(&type1)?;
        assert!(LeanExpr::is_sort(&ty2));

        // 6. is_def_eq with different types (should be false)
        let prop6 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let type2 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        assert!(!ctx.is_def_eq(&prop6, &type2)?);

        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}
