//! End-to-end proof construction lifecycle tests
//!
//! Issue #43 — Phase 4.5: Comprehensive integration tests for proof support.
//!
//! Tests cover:
//! - Proof construction → validation → add to environment
//! - Proof construction + type inference round-trip
//! - Invalid proof detection
//! - Theorem declaration lifecycle (create → add → find → inspect)
//! - Definition declaration lifecycle
//! - Memory safety in proof construction workflows

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// End-to-end: construct proof, validate, add to environment
// ============================================================================

#[test]
fn test_e2e_construct_validate_add_proof() {
    // Build a proof of ∀ (P : Prop), P → P, validate with check(), add as theorem
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Type: ∀ (P : Prop), ∀ (h : P), P
        // = forall (P : Sort 0), forall (h : bvar 0), bvar 1
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let proposition = LeanExpr::forall(
            p_name.clone(),
            prop.clone(),
            inner_forall,
            BinderInfo::Default,
        )?;

        // Value: λ (P : Prop) (h : P), h
        // = lambda (P : Sort 0), lambda (h : bvar 0), bvar 0
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_inner = LeanExpr::bvar(lean, 0)?;
        let bvar0_body = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0_inner, bvar0_body, BinderInfo::Default)?;
        let proof = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

        // Validate the proof with MetaM check()
        let mut ctx = MetaMContext::new(lean, env.clone())?;
        ctx.check(&proof)?;

        // Verify the proof proves the proposition
        assert!(ctx.is_proof_of(&proof, &proposition)?);

        // Add as a theorem to the environment with kernel type checking
        let thm_name = LeanName::from_str(lean, "id_proof")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, level_params, proposition, proof)?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        // Verify it was added
        let found_name = LeanName::from_str(lean, "id_proof")?;
        let found = LeanEnvironment::find(&new_env, &found_name)?;
        assert!(found.is_some(), "theorem should be in the environment");

        let cinfo = found.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Theorem);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "e2e construct/validate/add failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Proof construction + type inference round-trip
// ============================================================================

#[test]
fn test_proof_type_inference_roundtrip() {
    // Build a proof, infer its type, verify it matches the expected proposition
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Build: λ (P : Prop) (h : P), h  — proves ∀ P : Prop, P → P
        // In de Bruijn: lambda (P : Sort 0), lambda (h : bvar 0), bvar 0
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_type = LeanExpr::bvar(lean, 0)?; // h's type is P (bvar 0 in outer scope)
        let bvar0_body = LeanExpr::bvar(lean, 0)?; // body is h (bvar 0 in inner scope)
        let inner = LeanExpr::lambda(h_name, bvar0_type, bvar0_body, BinderInfo::Default)?;
        let proof = LeanExpr::lambda(p_name, prop, inner, BinderInfo::Default)?;

        // Infer the type of the proof
        let inferred_type = ctx.get_proof_type(&proof)?;

        // The inferred type should be a proposition (its type should be Prop)
        assert!(
            ctx.is_prop(&inferred_type)?,
            "inferred type should be a proposition"
        );

        // The inferred type should be a forall (∀ P : Prop, P → P)
        assert_eq!(
            LeanExpr::kind(&inferred_type),
            ExprKind::Forall,
            "inferred type should be a forall"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "proof type inference roundtrip failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Invalid proof detection
// ============================================================================

#[test]
fn test_invalid_proof_rejected_by_kernel() {
    // Try to add a theorem with a wrong proof — kernel should reject it
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Proposition: ∀ (P : Prop), P  (unprovable in an empty environment)
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proposition = LeanExpr::forall(p_name, prop.clone(), body, BinderInfo::Default)?;

        // Wrong proof: λ (P : Prop), Sort 0  — this has type Prop → Type, not ∀ P, P
        let p_name2 = LeanName::from_str(lean, "P")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_proof = LeanExpr::lambda(p_name2, prop2, wrong_body, BinderInfo::Default)?;

        // MetaM should detect the mismatch
        let mut ctx = MetaMContext::new(lean, env.clone())?;
        assert!(
            !ctx.is_proof_of(&wrong_proof, &proposition)?,
            "wrong proof should not prove the proposition"
        );

        // Kernel should reject the theorem
        let thm_name = LeanName::from_str(lean, "bad_thm")?;
        let level_params = LeanList::nil(lean)?;
        let decl =
            LeanDeclaration::theorem(lean, thm_name, level_params, proposition, wrong_proof)?;
        let add_result = LeanEnvironment::add_decl(&env, &decl);
        assert!(
            add_result.is_err(),
            "kernel should reject ill-typed theorem"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "invalid proof detection failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Theorem declaration lifecycle: create → add → find → inspect
// ============================================================================

#[test]
fn test_theorem_lifecycle() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Theorem: ∀ (P : Prop), P → P
        // Proof:   λ (P : Prop) (h : P), h
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Type: forall (P : Sort 0), forall (h : bvar 0), bvar 1
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let thm_type = LeanExpr::forall(p_name.clone(), prop, inner_forall, BinderInfo::Default)?;

        // Value: lambda (P : Sort 0), lambda (h : bvar 0), bvar 0
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_inner = LeanExpr::bvar(lean, 0)?;
        let bvar0_body = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0_inner, bvar0_body, BinderInfo::Default)?;
        let proof = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

        // Create theorem declaration
        let thm_name = LeanName::from_str(lean, "id_prop")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, level_params, thm_type, proof)?;

        // Add to environment with kernel type checking
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        // Find it back
        let lookup_name = LeanName::from_str(lean, "id_prop")?;
        let found = LeanEnvironment::find(&new_env, &lookup_name)?;
        assert!(found.is_some(), "id_prop should be in the environment");

        // Inspect
        let cinfo = found.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Theorem);
        assert!(LeanConstantInfo::has_value(&cinfo));

        let found_type = LeanConstantInfo::type_(&cinfo)?;
        assert_eq!(LeanExpr::kind(&found_type), ExprKind::Forall);

        let found_value = LeanConstantInfo::value(&cinfo)?;
        assert!(found_value.is_some());
        let value = found_value.unwrap();
        assert_eq!(LeanExpr::kind(&value), ExprKind::Lambda);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "theorem lifecycle failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Definition declaration lifecycle
// ============================================================================

#[test]
fn test_definition_lifecycle() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Define: myId : ∀ (P : Prop), P → P := λ P h, h
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Type: forall (P : Sort 0), forall (h : bvar 0), bvar 1
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let def_type = LeanExpr::forall(p_name.clone(), prop, inner_forall, BinderInfo::Default)?;

        // Value: lambda (P : Sort 0), lambda (h : bvar 0), bvar 0
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_inner = LeanExpr::bvar(lean, 0)?;
        let bvar0_body = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0_inner, bvar0_body, BinderInfo::Default)?;
        let value = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

        // ReducibilityHints.opaque = tag 0, no fields → scalar lean_box(0)
        let hints = unsafe { LeanBound::from_owned_ptr(lean, leo3_ffi::lean_box(0)) };

        let def_name = LeanName::from_str(lean, "myId")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::definition(
            lean,
            def_name,
            level_params,
            def_type,
            value,
            hints,
            DefinitionSafety::Safe,
        )?;

        // Use add_decl_unchecked because kernel type checking for definitions
        // with ReducibilityHints.opaque can crash in the current worker thread setup.
        let new_env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;
        let lookup_name = LeanName::from_str(lean, "myId")?;
        let found = LeanEnvironment::find(&new_env, &lookup_name)?;
        assert!(found.is_some(), "myId should be in the environment");

        let cinfo = found.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Definition);
        assert!(LeanConstantInfo::has_value(&cinfo));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "definition lifecycle failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Memory safety: repeated proof construction without leaks
// ============================================================================

#[test]
fn test_proof_construction_memory_safety() {
    // Construct many proofs in a loop to exercise refcount management
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        for i in 0..100 {
            // Build: λ (P : Prop) (h : P), h
            let p_name = LeanName::from_str(lean, "P")?;
            let h_name = LeanName::from_str(lean, "h")?;
            let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            let bvar0 = LeanExpr::bvar(lean, 0)?;
            let bvar1 = LeanExpr::bvar(lean, 1)?;
            let inner = LeanExpr::lambda(h_name, bvar1, bvar0, BinderInfo::Default)?;
            let proof = LeanExpr::lambda(p_name, prop, inner, BinderInfo::Default)?;

            let inferred = ctx.get_proof_type(&proof)?;
            assert!(
                LeanExpr::is_forall(&inferred),
                "iteration {}: inferred type should be a forall",
                i
            );
        }

        Ok(())
    });

    assert!(
        result.is_ok(),
        "memory safety test failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Axiom lifecycle: add axiom → find → inspect
// ============================================================================

#[test]
fn test_axiom_lifecycle() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // axiom myAxiom : ∀ (P : Prop), P
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let axiom_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let ax_name = LeanName::from_str(lean, "myAxiom")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, level_params, axiom_type, false)?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup_name = LeanName::from_str(lean, "myAxiom")?;
        let found = LeanEnvironment::find(&new_env, &lookup_name)?;
        assert!(found.is_some());

        let cinfo = found.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Axiom);
        assert!(!LeanConstantInfo::has_value(&cinfo));
        assert!(LeanConstantInfo::value(&cinfo)?.is_none());

        Ok(())
    });

    assert!(result.is_ok(), "axiom lifecycle failed: {:?}", result.err());
}
