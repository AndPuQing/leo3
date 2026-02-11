//! Tests for proof utility helpers: get_proof_type, is_proof_of, is_prop
//!
//! Issue #44 — Phase 4.3: Proof utility helpers

use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_get_proof_type_sort() {
    // The type of Prop (Sort 0) is Type (Sort 1)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let proof_type = ctx.get_proof_type(&prop)?;

        assert!(
            LeanExpr::is_sort(&proof_type),
            "Expected Sort, got {:?}",
            LeanExpr::kind(&proof_type)
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "get_proof_type(Sort 0) failed: {:?}",
        result.err()
    );
}

#[test]
fn test_is_proof_of_correct() {
    // λ (x : Prop), x is a proof of Prop → Prop.
    // is_proof_of should confirm this.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proof = LeanExpr::lambda(x_name, prop.clone(), body, BinderInfo::Default)?;

        // The type of (λ x : Prop, x) is (Prop → Prop), i.e., ∀ _ : Sort 0, Sort 0
        let anon = LeanName::from_str(lean, "")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let expected_type = LeanExpr::forall(anon, prop2, prop3, BinderInfo::Default)?;

        assert!(ctx.is_proof_of(&proof, &expected_type)?);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "is_proof_of correct failed: {:?}",
        result.err()
    );
}

#[test]
fn test_is_proof_of_wrong_prop() {
    // λ (x : Prop), x proves Prop → Prop, not Type → Type.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proof = LeanExpr::lambda(x_name, prop, body, BinderInfo::Default)?;

        // Wrong proposition: Type → Type (Sort 1 → Sort 1)
        let anon = LeanName::from_str(lean, "")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let type0b = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let wrong_prop = LeanExpr::forall(anon, type0, type0b, BinderInfo::Default)?;

        assert!(!ctx.is_proof_of(&proof, &wrong_prop)?);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "is_proof_of wrong prop failed: {:?}",
        result.err()
    );
}

#[test]
fn test_is_prop_sort0_expr() {
    // An expression whose type is Prop (Sort 0) is a proposition.
    // Prop → Prop has type Sort 1 (Type), so it's NOT a proposition.
    // But Prop itself has type Type, so it IS a proposition? No — Prop : Type, not Prop : Prop.
    //
    // Actually: is_prop checks if the *type* of the expression is Sort 0.
    // - Type of (Sort 0) = Sort 1 → not a prop
    // - Type of (λ x : Prop, x) = Prop → Prop : Sort 1 → not a prop
    //
    // We need an expression whose type lives in Prop. In an empty environment,
    // ∀ (P : Prop), P has type Prop (Sort 0). Let's use that.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // ∀ (P : Prop), P  — this is a proposition (its type is Prop)
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?; // P
        let forall_expr = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        assert!(
            ctx.is_prop(&forall_expr)?,
            "∀ P : Prop, P should be a proposition"
        );

        // Sort 0 (Prop) has type Sort 1 (Type), so it's NOT a proposition
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(
            !ctx.is_prop(&prop2)?,
            "Prop itself should not be a proposition"
        );

        Ok(())
    });

    assert!(result.is_ok(), "is_prop test failed: {:?}", result.err());
}
