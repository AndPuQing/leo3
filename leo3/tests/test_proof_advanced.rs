//! Advanced proof object integration tests
//!
//! Tests cover:
//! - Multi-step proof construction (composition of identity proofs)
//! - Proof with universe polymorphism (level parameters)
//! - Proof validation edge cases (wrong types, non-existent constants)
//! - Cross-environment proof sharing (same proof in different envs)
//! - Proofs with complex dependent types (nested foralls, higher-order)

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// Multi-step proof construction
// ============================================================================

/// Build the identity proof λ (P : Prop) (h : P), h and its type ∀ (P : Prop), P → P.
/// Returns (type, value).
fn build_id_proof<'l>(
    lean: Lean<'l>,
) -> LeanResult<(LeanBound<'l, LeanExpr>, LeanBound<'l, LeanExpr>)> {
    let p_name = LeanName::from_str(lean, "P")?;
    let h_name = LeanName::from_str(lean, "h")?;
    let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

    // Type: ∀ (P : Prop), ∀ (h : P), P
    let bvar0 = LeanExpr::bvar(lean, 0)?;
    let bvar1 = LeanExpr::bvar(lean, 1)?;
    let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
    let ty = LeanExpr::forall(
        p_name.clone(),
        prop.clone(),
        inner_forall,
        BinderInfo::Default,
    )?;

    // Value: λ (P : Prop) (h : P), h
    let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
    let bvar0_t = LeanExpr::bvar(lean, 0)?;
    let bvar0_b = LeanExpr::bvar(lean, 0)?;
    let inner_lambda = LeanExpr::lambda(h_name, bvar0_t, bvar0_b, BinderInfo::Default)?;
    let val = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

    Ok((ty, val))
}

#[test]
fn test_compose_two_identity_proofs() {
    // Add two identity theorems to the environment, then build a proof that
    // composes them: given h : P, apply id1 then id2.
    // Composition: λ (P : Prop) (h : P), id2 P (id1 P h)
    // This should type-check as ∀ (P : Prop), P → P.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let (id_type, id_value) = build_id_proof(lean)?;

        // Add id1
        let id1_name = LeanName::from_str(lean, "id1")?;
        let lp1 = LeanList::nil(lean)?;
        let decl1 =
            LeanDeclaration::theorem(lean, id1_name, lp1, id_type.clone(), id_value.clone())?;
        let env = LeanEnvironment::add_decl(&env, &decl1)?;

        // Add id2
        let id2_name = LeanName::from_str(lean, "id2")?;
        let lp2 = LeanList::nil(lean)?;
        let (id_type2, id_value2) = build_id_proof(lean)?;
        let decl2 = LeanDeclaration::theorem(lean, id2_name, lp2, id_type2, id_value2)?;
        let env = LeanEnvironment::add_decl(&env, &decl2)?;

        // Build composition: λ (P : Prop) (h : P), id2 P (id1 P h)
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let id1_const =
            LeanExpr::const_(lean, LeanName::from_str(lean, "id1")?, LeanList::nil(lean)?)?;
        let id2_const =
            LeanExpr::const_(lean, LeanName::from_str(lean, "id2")?, LeanList::nil(lean)?)?;

        // bvar 1 = P, bvar 0 = h (inside the two lambdas)
        let p_ref = LeanExpr::bvar(lean, 1)?;
        let h_ref = LeanExpr::bvar(lean, 0)?;

        // id1 P h
        let inner_app = LeanExpr::mk_app(&id1_const, &[&p_ref, &h_ref])?;
        // id2 P (id1 P h)
        let p_ref2 = LeanExpr::bvar(lean, 1)?;
        let outer_app = LeanExpr::mk_app(&id2_const, &[&p_ref2, &inner_app])?;

        let bvar0_type = LeanExpr::bvar(lean, 0)?;
        let inner_lam = LeanExpr::lambda(h_name, bvar0_type, outer_app, BinderInfo::Default)?;
        let composed = LeanExpr::lambda(p_name, prop, inner_lam, BinderInfo::Default)?;

        // Kernel-validate as a theorem
        let comp_name = LeanName::from_str(lean, "id_composed")?;
        let lp = LeanList::nil(lean)?;
        let comp_decl = LeanDeclaration::theorem(lean, comp_name, lp, id_type, composed)?;
        let final_env = LeanEnvironment::add_decl(&env, &comp_decl)?;

        // Verify it was added
        let lookup = LeanName::from_str(lean, "id_composed")?;
        let found = LeanEnvironment::find(&final_env, &lookup)?;
        assert!(found.is_some(), "composed theorem should be in env");
        assert_eq!(
            LeanConstantInfo::kind(&found.unwrap()),
            ConstantKind::Theorem
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "compose two identity proofs failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Universe polymorphism
// ============================================================================

#[test]
fn test_universe_polymorphic_identity() {
    // Build a universe-polymorphic identity:
    //   def polyId.{u} : ∀ (A : Sort u), A → A := fun A a => a
    // This must be a `def`, not a `theorem`, because ∀ (A : Sort u), A → A
    // has type Sort u, which is NOT Prop (unless u = 0). The kernel rejects
    // theorems whose type is not in Prop.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let u_name = LeanName::from_str(lean, "u")?;
        let u_level = LeanLevel::param(lean, u_name.clone())?;

        // Sort u
        let sort_u = LeanExpr::sort(lean, u_level)?;

        // Type: ∀ (A : Sort u), ∀ (a : A), A
        // = forall (A : Sort u), forall (a : bvar 0), bvar 1
        let a_name = LeanName::from_str(lean, "A")?;
        let a_arg_name = LeanName::from_str(lean, "a")?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(a_arg_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let poly_type = LeanExpr::forall(
            a_name.clone(),
            sort_u.clone(),
            inner_forall,
            BinderInfo::Default,
        )?;

        // Value: λ (A : Sort u) (a : A), a
        let sort_u2 = LeanExpr::sort(
            lean,
            LeanLevel::param(lean, LeanName::from_str(lean, "u")?)?,
        )?;
        let bvar0_t = LeanExpr::bvar(lean, 0)?;
        let bvar0_b = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(a_arg_name, bvar0_t, bvar0_b, BinderInfo::Default)?;
        let poly_value = LeanExpr::lambda(a_name, sort_u2, inner_lambda, BinderInfo::Default)?;

        // Level params list: [u]
        let nil = LeanList::nil(lean)?;
        let level_params = LeanList::cons(u_name.cast(), nil)?;

        let def_name = LeanName::from_str(lean, "polyId")?;
        // ReducibilityHints.opaque (tag 0, 0 fields = scalar lean_box(0))
        let hints = unsafe { LeanBound::from_owned_ptr(lean, leo3_ffi::lean_box(0)) };
        let decl = LeanDeclaration::definition(
            lean,
            def_name,
            level_params,
            poly_type,
            poly_value,
            hints,
            DefinitionSafety::Safe,
        )?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "polyId")?;
        let found = LeanEnvironment::find(&new_env, &lookup)?;
        assert!(found.is_some(), "polyId should be in the environment");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "universe polymorphic identity failed: {:?}",
        result.err()
    );
}

#[test]
fn test_universe_polymorphic_theorem_rejected_when_not_prop() {
    // Verify that the kernel correctly rejects a universe-polymorphic "theorem"
    // whose type is not in Prop. ∀ (A : Sort u), A → A has type Sort u,
    // which is only Prop when u = 0.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let u_name = LeanName::from_str(lean, "u")?;
        let u_level = LeanLevel::param(lean, u_name.clone())?;
        let sort_u = LeanExpr::sort(lean, u_level)?;

        let a_name = LeanName::from_str(lean, "A")?;
        let a_arg_name = LeanName::from_str(lean, "a")?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(a_arg_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let poly_type = LeanExpr::forall(
            a_name.clone(),
            sort_u.clone(),
            inner_forall,
            BinderInfo::Default,
        )?;

        let sort_u2 = LeanExpr::sort(
            lean,
            LeanLevel::param(lean, LeanName::from_str(lean, "u")?)?,
        )?;
        let bvar0_t = LeanExpr::bvar(lean, 0)?;
        let bvar0_b = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(a_arg_name, bvar0_t, bvar0_b, BinderInfo::Default)?;
        let poly_value = LeanExpr::lambda(a_name, sort_u2, inner_lambda, BinderInfo::Default)?;

        let nil = LeanList::nil(lean)?;
        let level_params = LeanList::cons(u_name.cast(), nil)?;

        let thm_name = LeanName::from_str(lean, "polyId")?;
        let decl = LeanDeclaration::theorem(lean, thm_name, level_params, poly_type, poly_value)?;

        // Kernel should reject: "theorem type is not Prop"
        let result = LeanEnvironment::add_decl(&env, &decl);
        assert!(
            result.is_err(),
            "kernel should reject theorem whose type is not Prop"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "universe polymorphic theorem rejection test failed: {:?}",
        result.err()
    );
}

#[test]
fn test_universe_polymorphic_two_params() {
    // def polyConst.{u, v} : ∀ (A : Sort u) (B : Sort v), A → B → A
    //   := fun A B a _b => a
    // Must be a `def` (not `theorem`) because the type is not in Prop.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let u_name = LeanName::from_str(lean, "u")?;
        let v_name = LeanName::from_str(lean, "v")?;
        let u_level = LeanLevel::param(lean, u_name.clone())?;
        let v_level = LeanLevel::param(lean, v_name.clone())?;

        let sort_u = LeanExpr::sort(lean, u_level)?;
        let sort_v = LeanExpr::sort(lean, v_level)?;

        // Type: ∀ (A : Sort u) (B : Sort v) (a : A) (b : B), A
        // de Bruijn: forall A:Sort u, forall B:Sort v, forall a:bvar1, forall b:bvar1, bvar3
        let a_name = LeanName::from_str(lean, "A")?;
        let b_name = LeanName::from_str(lean, "B")?;
        let a_arg = LeanName::from_str(lean, "a")?;
        let b_arg = LeanName::from_str(lean, "b")?;

        let bvar1_a = LeanExpr::bvar(lean, 1)?; // a's type is A (1 binder up)
        let bvar1_b = LeanExpr::bvar(lean, 1)?; // b's type is B (1 binder up)
        let bvar3 = LeanExpr::bvar(lean, 3)?; // body refers to A (3 binders up)

        let f4 = LeanExpr::forall(b_arg.clone(), bvar1_b, bvar3, BinderInfo::Default)?;
        let f3 = LeanExpr::forall(a_arg.clone(), bvar1_a, f4, BinderInfo::Default)?;
        let f2 = LeanExpr::forall(b_name.clone(), sort_v.clone(), f3, BinderInfo::Default)?;
        let poly_type = LeanExpr::forall(a_name.clone(), sort_u.clone(), f2, BinderInfo::Default)?;

        // Value: λ A B a _b => a
        // de Bruijn: lambda A:Sort u, lambda B:Sort v, lambda a:bvar1, lambda b:bvar1, bvar1
        let sort_u2 = LeanExpr::sort(
            lean,
            LeanLevel::param(lean, LeanName::from_str(lean, "u")?)?,
        )?;
        let sort_v2 = LeanExpr::sort(
            lean,
            LeanLevel::param(lean, LeanName::from_str(lean, "v")?)?,
        )?;
        let bvar1_at = LeanExpr::bvar(lean, 1)?;
        let bvar1_bt = LeanExpr::bvar(lean, 1)?;
        let bvar1_body = LeanExpr::bvar(lean, 1)?; // refers to a

        let l4 = LeanExpr::lambda(b_arg, bvar1_bt, bvar1_body, BinderInfo::Default)?;
        let l3 = LeanExpr::lambda(a_arg, bvar1_at, l4, BinderInfo::Default)?;
        let l2 = LeanExpr::lambda(b_name, sort_v2, l3, BinderInfo::Default)?;
        let poly_value = LeanExpr::lambda(a_name, sort_u2, l2, BinderInfo::Default)?;

        // Level params: [u, v]
        let nil = LeanList::nil(lean)?;
        let lp_v = LeanList::cons(v_name.cast(), nil)?;
        let level_params = LeanList::cons(u_name.cast(), lp_v)?;

        let def_name = LeanName::from_str(lean, "polyConst")?;
        // ReducibilityHints.opaque
        let hints = unsafe { LeanBound::from_owned_ptr(lean, leo3_ffi::lean_box(0)) };
        let decl = LeanDeclaration::definition(
            lean,
            def_name,
            level_params,
            poly_type,
            poly_value,
            hints,
            DefinitionSafety::Safe,
        )?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "polyConst")?;
        let found = LeanEnvironment::find(&new_env, &lookup)?;
        assert!(found.is_some(), "polyConst should be in the environment");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "universe polymorphic two params failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Proof validation edge cases
// ============================================================================

#[test]
fn test_kernel_rejects_type_mismatch_in_theorem() {
    // Theorem claims ∀ P, P → P but proof is λ P, P (wrong: returns Prop, not P)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let (id_type, _) = build_id_proof(lean)?;

        // Wrong proof: λ (P : Prop), P  — has type Prop → Prop, not ∀ P, P → P
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let wrong_proof = LeanExpr::lambda(p_name, prop, body, BinderInfo::Default)?;

        let thm_name = LeanName::from_str(lean, "bad_thm")?;
        let lp = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, lp, id_type, wrong_proof)?;
        let result = LeanEnvironment::add_decl(&env, &decl);
        assert!(result.is_err(), "kernel should reject type mismatch");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "type mismatch rejection failed: {:?}",
        result.err()
    );
}

#[test]
fn test_kernel_rejects_nonexistent_constant_in_proof() {
    // Proof references a constant that doesn't exist in the environment
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Type: ∀ (P : Prop), P → P
        let (id_type, _) = build_id_proof(lean)?;

        // Proof that references a non-existent constant "ghost"
        let ghost_const = LeanExpr::const_(
            lean,
            LeanName::from_str(lean, "ghost")?,
            LeanList::nil(lean)?,
        )?;

        let thm_name = LeanName::from_str(lean, "uses_ghost")?;
        let lp = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, lp, id_type, ghost_const)?;
        let result = LeanEnvironment::add_decl(&env, &decl);
        assert!(
            result.is_err(),
            "kernel should reject proof referencing non-existent constant"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "nonexistent constant rejection failed: {:?}",
        result.err()
    );
}

#[test]
fn test_metam_detects_wrong_proof_type() {
    // Use MetaMContext::is_proof_of to detect that a proof doesn't match
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Build λ (P : Prop) (h : P), h — proves ∀ P, P → P
        let (_, id_value) = build_id_proof(lean)?;

        // Claim it proves ∀ (P : Prop) (Q : Prop), P → Q (which it doesn't)
        let p_name = LeanName::from_str(lean, "P")?;
        let q_name = LeanName::from_str(lean, "Q")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?; // Q
        let bvar2 = LeanExpr::bvar(lean, 2)?; // P (2 binders up)

        let f_h = LeanExpr::forall(h_name, bvar2, bvar0, BinderInfo::Default)?;
        let f_q = LeanExpr::forall(q_name, prop2, f_h, BinderInfo::Default)?;
        let wrong_type = LeanExpr::forall(p_name, prop, f_q, BinderInfo::Default)?;

        assert!(
            !ctx.is_proof_of(&id_value, &wrong_type)?,
            "id proof should not prove ∀ P Q, P → Q"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "wrong proof type detection failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Cross-environment proof sharing
// ============================================================================

#[test]
fn test_same_proof_added_to_independent_environments() {
    // The same proof term can be added to two independent environments
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env1 = LeanEnvironment::empty(lean, 0)?;
        let env2 = LeanEnvironment::empty(lean, 0)?;

        let (id_type, id_value) = build_id_proof(lean)?;
        let (id_type2, id_value2) = build_id_proof(lean)?;

        // Add to env1 as "thm_a"
        let name1 = LeanName::from_str(lean, "thm_a")?;
        let lp1 = LeanList::nil(lean)?;
        let decl1 = LeanDeclaration::theorem(lean, name1, lp1, id_type, id_value)?;
        let env1 = LeanEnvironment::add_decl(&env1, &decl1)?;

        // Add to env2 as "thm_b"
        let name2 = LeanName::from_str(lean, "thm_b")?;
        let lp2 = LeanList::nil(lean)?;
        let decl2 = LeanDeclaration::theorem(lean, name2, lp2, id_type2, id_value2)?;
        let env2 = LeanEnvironment::add_decl(&env2, &decl2)?;

        // env1 has thm_a
        let lookup_a = LeanName::from_str(lean, "thm_a")?;
        assert!(LeanEnvironment::find(&env1, &lookup_a)?.is_some());

        // env2 has thm_b
        let lookup_b = LeanName::from_str(lean, "thm_b")?;
        assert!(LeanEnvironment::find(&env2, &lookup_b)?.is_some());

        Ok(())
    });

    assert!(
        result.is_ok(),
        "cross-environment proof sharing failed: {:?}",
        result.err()
    );
}

#[test]
fn test_environment_immutability_after_add_decl() {
    // Adding a decl returns a new env; the original is unchanged.
    // We verify by checking the original env does NOT contain the new theorem.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let original_env = LeanEnvironment::empty(lean, 0)?;
        let (id_type, id_value) = build_id_proof(lean)?;

        let name = LeanName::from_str(lean, "added_thm")?;
        let lp = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, name, lp, id_type, id_value)?;
        let _new_env = LeanEnvironment::add_decl(&original_env, &decl)?;

        // Original env should NOT have the theorem
        let lookup = LeanName::from_str(lean, "added_thm")?;
        assert!(
            LeanEnvironment::find(&original_env, &lookup)?.is_none(),
            "original env should be unchanged"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "environment immutability test failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Complex dependent types
// ============================================================================

#[test]
fn test_nested_forall_proof() {
    // Prove: ∀ (P Q : Prop), P → Q → P
    // Proof: λ P Q h _hq, h
    // de Bruijn type:  forall P:Sort0, forall Q:Sort0, forall h:bvar1, forall hq:bvar1, bvar3
    // de Bruijn value: lambda P:Sort0, lambda Q:Sort0, lambda h:bvar1, lambda hq:bvar1, bvar1
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let p_name = LeanName::from_str(lean, "P")?;
        let q_name = LeanName::from_str(lean, "Q")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let hq_name = LeanName::from_str(lean, "hq")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Type
        let bvar1_h = LeanExpr::bvar(lean, 1)?; // h's type is P
        let bvar1_hq = LeanExpr::bvar(lean, 1)?; // hq's type is Q
        let bvar3 = LeanExpr::bvar(lean, 3)?; // body refers to P

        let f4 = LeanExpr::forall(hq_name.clone(), bvar1_hq, bvar3, BinderInfo::Default)?;
        let f3 = LeanExpr::forall(h_name.clone(), bvar1_h, f4, BinderInfo::Default)?;
        let f2 = LeanExpr::forall(q_name.clone(), prop2, f3, BinderInfo::Default)?;
        let thm_type = LeanExpr::forall(p_name.clone(), prop, f2, BinderInfo::Default)?;

        // Value
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop4 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar1_ht = LeanExpr::bvar(lean, 1)?;
        let bvar1_hqt = LeanExpr::bvar(lean, 1)?;
        let bvar1_body = LeanExpr::bvar(lean, 1)?; // refers to h

        let l4 = LeanExpr::lambda(hq_name, bvar1_hqt, bvar1_body, BinderInfo::Default)?;
        let l3 = LeanExpr::lambda(h_name, bvar1_ht, l4, BinderInfo::Default)?;
        let l2 = LeanExpr::lambda(q_name, prop4, l3, BinderInfo::Default)?;
        let thm_value = LeanExpr::lambda(p_name, prop3, l2, BinderInfo::Default)?;

        // Validate with MetaM
        let mut ctx = MetaMContext::new(lean, env.clone())?;
        assert!(ctx.is_proof_of(&thm_value, &thm_type)?);

        // Kernel validate
        let name = LeanName::from_str(lean, "const_proof")?;
        let lp = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, name, lp, thm_type, thm_value)?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "const_proof")?;
        assert!(LeanEnvironment::find(&new_env, &lookup)?.is_some());

        Ok(())
    });

    assert!(
        result.is_ok(),
        "nested forall proof failed: {:?}",
        result.err()
    );
}

#[test]
fn test_higher_order_proof() {
    // Prove: ∀ (P : Prop) (f : P → P), P → P
    // Proof: λ P f h, f h
    // de Bruijn type:
    //   forall P:Sort0,
    //     forall f:(forall _:bvar0, bvar1),   -- f : P → P
    //       forall h:bvar1,                    -- h : P
    //         bvar2                            -- body: P
    // de Bruijn value:
    //   lambda P:Sort0,
    //     lambda f:(forall _:bvar0, bvar1),
    //       lambda h:bvar1,
    //         app(bvar1, bvar0)                -- f h
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let p_name = LeanName::from_str(lean, "P")?;
        let f_name = LeanName::from_str(lean, "f")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let anon = LeanName::from_str(lean, "")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // f's type: P → P = forall (_:bvar0), bvar1
        let bvar0_fd = LeanExpr::bvar(lean, 0)?;
        let bvar1_fb = LeanExpr::bvar(lean, 1)?;
        let f_type = LeanExpr::forall(anon.clone(), bvar0_fd, bvar1_fb, BinderInfo::Default)?;

        // h's type: P = bvar 1 (P is 2 binders up, but h is 1 binder inside f's scope)
        let bvar1_h = LeanExpr::bvar(lean, 1)?;
        // body: P = bvar 2
        let bvar2_body = LeanExpr::bvar(lean, 2)?;

        let f3 = LeanExpr::forall(h_name.clone(), bvar1_h, bvar2_body, BinderInfo::Default)?;
        let f2 = LeanExpr::forall(f_name.clone(), f_type.clone(), f3, BinderInfo::Default)?;
        let thm_type = LeanExpr::forall(p_name.clone(), prop.clone(), f2, BinderInfo::Default)?;

        // Value: λ P f h, f h
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let anon2 = LeanName::from_str(lean, "")?;
        let bvar0_fd2 = LeanExpr::bvar(lean, 0)?;
        let bvar1_fb2 = LeanExpr::bvar(lean, 1)?;
        let f_type2 = LeanExpr::forall(anon2, bvar0_fd2, bvar1_fb2, BinderInfo::Default)?;

        let bvar1_ht = LeanExpr::bvar(lean, 1)?; // h's type: P
        let bvar1_f = LeanExpr::bvar(lean, 1)?; // f
        let bvar0_h = LeanExpr::bvar(lean, 0)?; // h
        let app_fh = LeanExpr::app(&bvar1_f, &bvar0_h)?;

        let l3 = LeanExpr::lambda(h_name, bvar1_ht, app_fh, BinderInfo::Default)?;
        let l2 = LeanExpr::lambda(f_name, f_type2, l3, BinderInfo::Default)?;
        let thm_value = LeanExpr::lambda(p_name, prop2, l2, BinderInfo::Default)?;

        // Validate
        let mut ctx = MetaMContext::new(lean, env.clone())?;
        ctx.check(&thm_value)?;
        assert!(ctx.is_proof_of(&thm_value, &thm_type)?);

        // Kernel validate
        let name = LeanName::from_str(lean, "apply_f")?;
        let lp = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, name, lp, thm_type, thm_value)?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "apply_f")?;
        assert!(LeanEnvironment::find(&new_env, &lookup)?.is_some());

        Ok(())
    });

    assert!(
        result.is_ok(),
        "higher order proof failed: {:?}",
        result.err()
    );
}

// ============================================================================
// De Bruijn index correctness with explicit forall vs arrow
// ============================================================================

#[test]
fn test_explicit_forall_vs_arrow_de_bruijn() {
    // Verify that explicit forall correctly handles bound variables
    // where arrow would shift indices incorrectly.
    //
    // Build: ∀ (P : Prop), P → P
    // With explicit forall: forall P:Sort0, forall h:bvar0, bvar1
    // With arrow (WRONG for bound vars): arrow would shift bvar indices in body
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Correct: explicit forall
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner = LeanExpr::forall(h_name, bvar0, bvar1, BinderInfo::Default)?;
        let correct_type = LeanExpr::forall(p_name, prop, inner, BinderInfo::Default)?;

        // This should be a proposition
        assert!(
            ctx.is_prop(&correct_type)?,
            "∀ P : Prop, P → P should be a proposition"
        );

        // The type should be well-formed (check doesn't error)
        ctx.check(&correct_type)?;

        Ok(())
    });

    assert!(
        result.is_ok(),
        "explicit forall vs arrow test failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Definitional equality of proof terms
// ============================================================================

#[test]
fn test_def_eq_alpha_equivalent_proofs() {
    // Two proofs that differ only in binder names should be def-eq
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // λ (P : Prop) (h : P), h
        let p1 = LeanName::from_str(lean, "P")?;
        let h1 = LeanName::from_str(lean, "h")?;
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_t1 = LeanExpr::bvar(lean, 0)?;
        let bvar0_b1 = LeanExpr::bvar(lean, 0)?;
        let inner1 = LeanExpr::lambda(h1, bvar0_t1, bvar0_b1, BinderInfo::Default)?;
        let proof1 = LeanExpr::lambda(p1, prop1, inner1, BinderInfo::Default)?;

        // λ (A : Prop) (x : A), x  — same proof, different names
        let a1 = LeanName::from_str(lean, "A")?;
        let x1 = LeanName::from_str(lean, "x")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_t2 = LeanExpr::bvar(lean, 0)?;
        let bvar0_b2 = LeanExpr::bvar(lean, 0)?;
        let inner2 = LeanExpr::lambda(x1, bvar0_t2, bvar0_b2, BinderInfo::Default)?;
        let proof2 = LeanExpr::lambda(a1, prop2, inner2, BinderInfo::Default)?;

        assert!(
            ctx.is_def_eq(&proof1, &proof2)?,
            "alpha-equivalent proofs should be def-eq"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "def eq alpha equivalent proofs failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Multiple theorems building on each other
// ============================================================================

#[test]
fn test_multiple_theorems_sequential_add() {
    // Add two independent theorems to the same environment, verify the second is present.
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let (id_type, id_value) = build_id_proof(lean)?;

        let id1_name = LeanName::from_str(lean, "id1")?;
        let lp1 = LeanList::nil(lean)?;
        let decl1 =
            LeanDeclaration::theorem(lean, id1_name, lp1, id_type.clone(), id_value.clone())?;
        let env = LeanEnvironment::add_decl(&env, &decl1)?;

        let id2_name = LeanName::from_str(lean, "id2")?;
        let lp2 = LeanList::nil(lean)?;
        let (id_type2, id_value2) = build_id_proof(lean)?;
        let decl2 = LeanDeclaration::theorem(lean, id2_name, lp2, id_type2, id_value2)?;
        let env = LeanEnvironment::add_decl(&env, &decl2)?;

        // Verify the second theorem is present (implies env accumulated both)
        let l2 = LeanName::from_str(lean, "id2")?;
        let found = LeanEnvironment::find(&env, &l2)?;
        assert!(found.is_some(), "id2 should be in the environment");
        assert_eq!(
            LeanConstantInfo::kind(&found.unwrap()),
            ConstantKind::Theorem
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "multiple theorems sequential add failed: {:?}",
        result.err()
    );
}
