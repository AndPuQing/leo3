//! Error handling boundary integration tests
//!
//! Tests that Lean exceptions are properly caught, converted to Rust errors,
//! and that the runtime remains usable after errors.

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// Kernel exceptions caught in Rust
// ============================================================================

#[test]
fn test_kernel_rejects_ill_typed_theorem() {
    // Theorem with wrong proof type → kernel should return Err
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Proposition: ∀ (P : Prop), P  (not provable)
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proposition = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        // Wrong proof: λ (P : Prop), Prop  (has type Prop → Type, not ∀ P, P)
        let p2 = LeanName::from_str(lean, "P")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_proof = LeanExpr::lambda(p2, prop2, wrong_body, BinderInfo::Default)?;

        let thm_name = LeanName::from_str(lean, "bad_thm")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, levels, proposition, wrong_proof)?;
        let add_result = LeanEnvironment::add_decl(&env, &decl);

        assert!(
            add_result.is_err(),
            "kernel should reject ill-typed theorem"
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
fn test_kernel_rejects_duplicate_declaration() {
    // Adding the same name twice → "already declared"
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // axiom myAx : ∀ (P : Prop), P
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let ax_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let ax_name = LeanName::from_str(lean, "myAx")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, levels, ax_type.clone(), false)?;
        let env2 = LeanEnvironment::add_decl(&env, &decl)?;

        // Try to add the same name again
        let ax_name2 = LeanName::from_str(lean, "myAx")?;
        let levels2 = LeanList::nil(lean)?;
        let decl2 = LeanDeclaration::axiom(lean, ax_name2, levels2, ax_type, false)?;
        let dup_result = LeanEnvironment::add_decl(&env2, &decl2);

        assert!(
            dup_result.is_err(),
            "duplicate declaration should be rejected"
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Exception message preservation across the FFI boundary
// ============================================================================

#[test]
fn test_kernel_error_message_contains_reason() {
    // Kernel errors should contain a descriptive message
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Build an ill-typed theorem so the kernel rejects it
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proposition = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let p2 = LeanName::from_str(lean, "P")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_proof = LeanExpr::lambda(p2, prop2, wrong_body, BinderInfo::Default)?;

        let thm_name = LeanName::from_str(lean, "msg_test")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, levels, proposition, wrong_proof)?;
        let add_result = LeanEnvironment::add_decl(&env, &decl);
        let err = match add_result {
            Err(e) => e,
            Ok(_) => panic!("expected kernel error for ill-typed theorem"),
        };

        let msg = format!("{}", err);
        assert!(!msg.is_empty(), "error message should not be empty");
        // Kernel errors are wrapped as FFI errors with "kernel type check failed: ..."
        assert!(
            msg.contains("kernel type check failed"),
            "error should mention kernel type check, got: {}",
            msg
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
fn test_duplicate_decl_error_message() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let ax_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let ax_name = LeanName::from_str(lean, "dupTest")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, levels, ax_type.clone(), false)?;
        let env2 = LeanEnvironment::add_decl(&env, &decl)?;

        let ax_name2 = LeanName::from_str(lean, "dupTest")?;
        let levels2 = LeanList::nil(lean)?;
        let decl2 = LeanDeclaration::axiom(lean, ax_name2, levels2, ax_type, false)?;
        let err = match LeanEnvironment::add_decl(&env2, &decl2) {
            Err(e) => e,
            Ok(_) => panic!("expected 'already declared' error"),
        };

        let msg = format!("{}", err);
        assert!(
            msg.contains("already declared"),
            "duplicate decl error should say 'already declared', got: {}",
            msg
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
fn test_add_decl_unchecked_rejects_duplicate() {
    // add_decl_unchecked should return Err on duplicate names, not SIGABRT
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let ax_name = LeanName::from_str(lean, "dupUnchecked")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, levels, prop.clone(), false)?;
        let env2 = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // Try to add the same name again via unchecked path
        let ax_name2 = LeanName::from_str(lean, "dupUnchecked")?;
        let levels2 = LeanList::nil(lean)?;
        let decl2 = LeanDeclaration::axiom(lean, ax_name2, levels2, prop, false)?;
        let dup_result = LeanEnvironment::add_decl_unchecked(&env2, &decl2);

        assert!(
            dup_result.is_err(),
            "duplicate unchecked declaration should be rejected"
        );
        let err = match dup_result {
            Err(e) => e,
            Ok(_) => panic!("expected 'already declared' error"),
        };
        let msg = format!("{}", err);
        assert!(
            msg.contains("already declared"),
            "error should say 'already declared', got: {}",
            msg
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Elaborator / MetaM exceptions caught in Rust
// ============================================================================

#[test]
fn test_metam_check_rejects_ill_typed_expr() {
    // MetaM check() on an ill-typed expression should return Err
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // (λ x : Sort 2, x) applied to Sort 0 — type mismatch
        let x_name = LeanName::from_str(lean, "x")?;
        let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
        let sort2 = LeanExpr::sort(lean, level2)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, sort2, body, BinderInfo::Default)?;

        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bad_app = LeanExpr::app(&lambda, &prop)?;

        let check_result = ctx.check(&bad_app);
        assert!(
            check_result.is_err(),
            "check() should reject ill-typed application"
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Recovery after errors — runtime still usable
// ============================================================================

#[test]
fn test_recovery_after_kernel_error() {
    // After a kernel error, the environment should still be usable
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // First: try to add an ill-typed theorem (should fail)
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let bad_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let p2 = LeanName::from_str(lean, "P")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_proof = LeanExpr::lambda(p2, prop2, wrong_body, BinderInfo::Default)?;

        let bad_name = LeanName::from_str(lean, "bad")?;
        let levels = LeanList::nil(lean)?;
        let bad_decl = LeanDeclaration::theorem(lean, bad_name, levels, bad_type, wrong_proof)?;
        let bad_result = LeanEnvironment::add_decl(&env, &bad_decl);
        assert!(bad_result.is_err());

        // Second: add a valid axiom (should succeed on the original env)
        let q_name = LeanName::from_str(lean, "Q")?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body3 = LeanExpr::bvar(lean, 0)?;
        let good_type = LeanExpr::forall(q_name, prop3, body3, BinderInfo::Default)?;

        let good_name = LeanName::from_str(lean, "good_axiom")?;
        let levels2 = LeanList::nil(lean)?;
        let good_decl = LeanDeclaration::axiom(lean, good_name, levels2, good_type, false)?;
        let new_env = LeanEnvironment::add_decl(&env, &good_decl)?;

        let lookup = LeanName::from_str(lean, "good_axiom")?;
        let found = LeanEnvironment::find(&new_env, &lookup)?;
        assert!(
            found.is_some(),
            "valid axiom should be in the environment after prior error"
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
fn test_recovery_after_metam_error() {
    // After a MetaM error, the context should still be usable
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        // Trigger an error: check an ill-typed expression
        let x_name = LeanName::from_str(lean, "x")?;
        let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
        let sort2 = LeanExpr::sort(lean, level2)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, sort2, body, BinderInfo::Default)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bad_app = LeanExpr::app(&lambda, &prop)?;
        assert!(ctx.check(&bad_app).is_err());

        // Now do a valid operation on the same context
        let good_expr = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        ctx.check(&good_expr)?;
        let ty = ctx.infer_type(&good_expr)?;
        assert!(LeanExpr::is_sort(&ty));

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Sequential operations: some fail, some succeed
// ============================================================================

#[test]
fn test_sequential_mixed_success_and_failure() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;

        let mut successes = 0u32;
        let mut failures = 0u32;

        for i in 0..10 {
            if i % 3 == 0 {
                // Ill-typed: (λ x : Sort 2, x) Sort 0
                let x_name = LeanName::from_str(lean, "x")?;
                let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
                let sort2 = LeanExpr::sort(lean, level2)?;
                let body = LeanExpr::bvar(lean, 0)?;
                let lambda = LeanExpr::lambda(x_name, sort2, body, BinderInfo::Default)?;
                let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
                let bad_app = LeanExpr::app(&lambda, &prop)?;
                assert!(ctx.check(&bad_app).is_err());
                failures += 1;
            } else {
                // Well-typed: Sort(i)
                let mut level = LeanLevel::zero(lean)?;
                for _ in 0..i {
                    level = LeanLevel::succ(level)?;
                }
                let sort = LeanExpr::sort(lean, level)?;
                ctx.check(&sort)?;
                successes += 1;
            }
        }

        assert!(successes > 0);
        assert!(failures > 0);

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Type mismatch errors with meaningful messages
// ============================================================================

#[test]
fn test_type_mismatch_error_from_kernel() {
    // A theorem whose proof type doesn't match the declared type
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Declared type: Prop → Prop (∀ _ : Sort 0, Sort 0)
        let prop1 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let declared_type = LeanExpr::arrow(prop1, prop2)?;

        // Proof: λ (x : Type), x  — has type Type → Type, not Prop → Prop
        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let proof = LeanExpr::lambda(x_name, type0, body, BinderInfo::Default)?;

        let thm_name = LeanName::from_str(lean, "mismatch_thm")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, levels, declared_type, proof)?;
        let err = match LeanEnvironment::add_decl(&env, &decl) {
            Err(e) => e,
            Ok(_) => panic!("expected kernel error for type mismatch"),
        };

        let msg = format!("{}", err);
        // Should be a kernel type check failure
        assert!(
            msg.contains("kernel type check failed"),
            "type mismatch should produce kernel error, got: {}",
            msg
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
fn test_theorem_type_not_prop_error() {
    // A "theorem" whose type is Type instead of Prop → kernel rejects
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Type: Sort 1 (= Type, not a Prop)
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        // Value: Sort 0 (= Prop, which has type Type)
        let value = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let thm_name = LeanName::from_str(lean, "not_a_prop")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, levels, type0, value)?;
        let err = match LeanEnvironment::add_decl(&env, &decl) {
            Err(e) => e,
            Ok(_) => panic!("expected 'theorem type is not Prop' error"),
        };

        let msg = format!("{}", err);
        assert!(
            msg.contains("theorem type is not Prop"),
            "theorem with non-Prop type should say 'theorem type is not Prop', got: {}",
            msg
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Error propagation chains
// ============================================================================

#[test]
fn test_error_propagation_with_question_mark() {
    // Errors from inner operations propagate correctly via ?
    let inner = || -> LeanResult<()> {
        leo3::test_with_lean(|lean| {
            let env = LeanEnvironment::empty(lean, 0)?;

            let p_name = LeanName::from_str(lean, "P")?;
            let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            let body = LeanExpr::bvar(lean, 0)?;
            let bad_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

            let p2 = LeanName::from_str(lean, "P")?;
            let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            let wrong_proof = LeanExpr::lambda(p2, prop2, wrong_body, BinderInfo::Default)?;

            let thm_name = LeanName::from_str(lean, "prop_test")?;
            let levels = LeanList::nil(lean)?;
            let decl = LeanDeclaration::theorem(lean, thm_name, levels, bad_type, wrong_proof)?;
            // This should fail and propagate via ?
            let _env2 = LeanEnvironment::add_decl(&env, &decl)?;

            Ok(())
        })
    };

    let result = inner();
    assert!(result.is_err(), "error should propagate through ?");
    let err = result.unwrap_err();
    // The error should be displayable and debuggable
    let display = format!("{}", err);
    let debug = format!("{:?}", err);
    assert!(!display.is_empty());
    assert!(!debug.is_empty());
}

// ============================================================================
// LeanError variant construction and Display
// ============================================================================

#[test]
fn test_lean_error_display_variants() {
    let conv = LeanError::conversion("bad nat");
    assert_eq!(format!("{}", conv), "Conversion error: bad nat");

    let rt = LeanError::runtime("init failed");
    assert_eq!(format!("{}", rt), "Lean runtime error: init failed");

    let ffi = LeanError::ffi("null pointer");
    assert_eq!(format!("{}", ffi), "FFI error: null pointer");

    let exc = LeanError::exception(false, "unknown free variable");
    assert_eq!(format!("{}", exc), "Lean exception: unknown free variable");

    let internal = LeanError::exception(true, "internal panic");
    assert_eq!(
        format!("{}", internal),
        "Lean internal exception: internal panic"
    );

    let other = LeanError::other("something else");
    assert_eq!(format!("{}", other), "Error: something else");
}

#[test]
fn test_lean_error_is_std_error() {
    let err = LeanError::ffi("test");
    let _: &dyn std::error::Error = &err;
}

// ============================================================================
// Resource cleanup on error paths (environment not corrupted)
// ============================================================================

#[test]
fn test_environment_not_corrupted_after_errors() {
    // A failed add_decl should not corrupt the environment
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Add a valid axiom first
        let q_name = LeanName::from_str(lean, "Q")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let ax_type = LeanExpr::forall(q_name, prop, body, BinderInfo::Default)?;
        let ax_name = LeanName::from_str(lean, "validAx")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, levels, ax_type, false)?;
        let env_with_ax = LeanEnvironment::add_decl(&env, &decl)?;

        // Try one bad declaration against env_with_ax
        let p_name = LeanName::from_str(lean, "P")?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body2 = LeanExpr::bvar(lean, 0)?;
        let bad_type = LeanExpr::forall(p_name, prop2, body2, BinderInfo::Default)?;

        let p2 = LeanName::from_str(lean, "P")?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_body = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let wrong_proof = LeanExpr::lambda(p2, prop3, wrong_body, BinderInfo::Default)?;

        let bad_name = LeanName::from_str(lean, "bad_0")?;
        let levels2 = LeanList::nil(lean)?;
        let bad_decl = LeanDeclaration::theorem(lean, bad_name, levels2, bad_type, wrong_proof)?;
        assert!(LeanEnvironment::add_decl(&env_with_ax, &bad_decl).is_err());

        // The original axiom should still be findable
        let lookup = LeanName::from_str(lean, "validAx")?;
        let found = LeanEnvironment::find(&env_with_ax, &lookup)?;
        assert!(
            found.is_some(),
            "valid axiom should survive after failed add_decl"
        );

        // The bad declaration should not be present
        let bad_lookup = LeanName::from_str(lean, "bad_0")?;
        let not_found = LeanEnvironment::find(&env_with_ax, &bad_lookup)?;
        assert!(
            not_found.is_none(),
            "bad_0 should not be in the environment"
        );

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============================================================================
// Multiple fresh contexts after errors
// ============================================================================

#[test]
fn test_fresh_context_after_error() {
    // Creating a new MetaMContext after errors on a previous one should work
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // First context: trigger an error
        {
            let mut ctx1 = MetaMContext::new(lean, env.clone())?;
            let x_name = LeanName::from_str(lean, "x")?;
            let level2 = LeanLevel::succ(LeanLevel::one(lean)?)?;
            let sort2 = LeanExpr::sort(lean, level2)?;
            let body = LeanExpr::bvar(lean, 0)?;
            let lambda = LeanExpr::lambda(x_name, sort2, body, BinderInfo::Default)?;
            let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            let bad_app = LeanExpr::app(&lambda, &prop)?;
            assert!(ctx1.check(&bad_app).is_err());
        }

        // Second context: should work fine
        {
            let mut ctx2 = MetaMContext::new(lean, env)?;
            let good = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
            ctx2.check(&good)?;
            let ty = ctx2.infer_type(&good)?;
            assert!(LeanExpr::is_sort(&ty));
        }

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}
