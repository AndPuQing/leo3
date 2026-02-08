//! Integration tests for MetaMContext (Phase 1 MetaM integration)
//!
//! These tests exercise the high-level `MetaMContext` API that bundles
//! `Core.Context`, `Core.State`, `Meta.Context`, and `Meta.State` for
//! running MetaM computations from Rust.
//!
//! Note: A full integration test that runs a real MetaM computation
//! (e.g., `inferType`) requires Phase 2 FFI bindings which aren't
//! wired up yet. The `run()` tests here use synthetic computations.

use leo3::meta::*;
use leo3::prelude::*;

#[test]
fn test_metam_context_creation() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let ctx = MetaMContext::new(lean, env)?;

        // Environment should be accessible and non-null
        assert!(!ctx.env().as_ptr().is_null());

        // Lean token should be valid
        let _lean = ctx.lean();

        Ok(())
    });

    assert!(
        result.is_ok(),
        "MetaMContext creation failed: {:?}",
        result.err()
    );
}

#[test]
fn test_metam_context_accessors() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let env_ptr = env.as_ptr();
        let ctx = MetaMContext::new(lean, env)?;

        // env() should return the same environment we passed in
        assert_eq!(
            ctx.env().as_ptr(),
            env_ptr,
            "env() should return the environment passed to new()"
        );

        // lean() should return a valid token
        let lean_token = ctx.lean();
        // Verify the token works by creating a Lean object with it
        let _name = LeanName::from_str(lean_token, "test")?;

        Ok(())
    });

    assert!(
        result.is_ok(),
        "MetaMContext accessors failed: {:?}",
        result.err()
    );
}

#[test]
fn test_metam_context_with_different_trust_levels() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Trust level 0 (default, fully checked)
        let env0 = LeanEnvironment::empty(lean, 0)?;
        let ctx0 = MetaMContext::new(lean, env0)?;
        assert!(!ctx0.env().as_ptr().is_null());

        // Trust level 1 (skip some checks)
        let env1 = LeanEnvironment::empty(lean, 1)?;
        let ctx1 = MetaMContext::new(lean, env1)?;
        assert!(!ctx1.env().as_ptr().is_null());

        // The two contexts should have different environments
        assert_ne!(
            ctx0.env().as_ptr(),
            ctx1.env().as_ptr(),
            "Different trust levels should produce different environments"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "MetaMContext trust level test failed: {:?}",
        result.err()
    );
}

#[test]
fn test_metam_context_multiple_independent() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create two independent MetaMContexts
        let env1 = LeanEnvironment::empty(lean, 0)?;
        let env2 = LeanEnvironment::empty(lean, 0)?;

        let ctx1 = MetaMContext::new(lean, env1)?;
        let ctx2 = MetaMContext::new(lean, env2)?;

        // Both should be valid and independent
        assert!(!ctx1.env().as_ptr().is_null());
        assert!(!ctx2.env().as_ptr().is_null());
        assert_ne!(
            ctx1.env().as_ptr(),
            ctx2.env().as_ptr(),
            "Independent contexts should have distinct environment pointers"
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Multiple MetaMContext test failed: {:?}",
        result.err()
    );
}

// Note: Full `MetaMContext::run()` integration tests require Phase 2 FFI
// bindings (e.g., `lean_meta_infer_type`) to construct real MetaM computations.
// The unit tests for `handle_eio_result` and `extract_message_data` in
// `leo3/src/meta/metam.rs` cover the run() result-handling logic with
// synthetic Except objects. See also `meta_eio_error.rs` for LeanError::Exception
// formatting tests.
