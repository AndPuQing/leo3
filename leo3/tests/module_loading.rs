//! Tests for environment loading, declaration querying, and module infrastructure.
//!
//! These tests verify that environments can be created, populated with declarations,
//! and queried for constant information including kinds, types, and values.

use leo3::meta::*;
use leo3::prelude::*;

// ============ Environment Creation and Basic Queries ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_empty_environment_find_returns_none() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let name = LeanName::from_str(lean, "NonExistent")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(
            found.is_none(),
            "empty env should not contain any constants"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_empty_environment_hierarchical_name_not_found() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        let name = LeanName::from_components(lean, "Nat.add")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(found.is_none(), "empty env should not contain Nat.add");

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Adding and Querying Axioms ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_axiom_and_query_kind() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        // Add an axiom: axiom myAx : Prop
        let name = LeanName::from_str(lean, "myAx")?;
        let level_params = LeanList::nil(lean)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let decl = LeanDeclaration::axiom(lean, name, level_params, prop, false)?;
        let new_env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "myAx")?;
        let found = LeanEnvironment::find(&new_env, &lookup)?;
        assert!(found.is_some(), "axiom should be found");

        let cinfo = found.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Axiom);
        assert!(!LeanConstantInfo::has_value(&cinfo));

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_axiom_type_is_preserved() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // axiom myAx : ∀ (P : Prop), P
        let p_name = LeanName::from_str(lean, "P")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let ax_type = LeanExpr::forall(p_name, prop, body, BinderInfo::Default)?;

        let ax_name = LeanName::from_str(lean, "myAx")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, level_params, ax_type, false)?;
        let new_env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "myAx")?;
        let cinfo = LeanEnvironment::find(&new_env, &lookup)?.unwrap();
        let found_type = LeanConstantInfo::type_(&cinfo)?;
        assert!(
            LeanExpr::is_forall(&found_type),
            "axiom type should be a forall"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Adding and Querying Theorems ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_theorem_and_query_value() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // theorem id_prop : ∀ (P : Prop), P → P := λ P h, h
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let thm_type = LeanExpr::forall(
            p_name.clone(),
            prop.clone(),
            inner_forall,
            BinderInfo::Default,
        )?;

        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_inner = LeanExpr::bvar(lean, 0)?;
        let bvar0_body = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0_inner, bvar0_body, BinderInfo::Default)?;
        let proof = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

        let thm_name = LeanName::from_str(lean, "id_prop")?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::theorem(lean, thm_name, level_params, thm_type, proof)?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "id_prop")?;
        let cinfo = LeanEnvironment::find(&new_env, &lookup)?.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Theorem);
        assert!(LeanConstantInfo::has_value(&cinfo));

        let value = LeanConstantInfo::value(&cinfo)?;
        assert!(value.is_some(), "theorem should have a value");
        assert!(
            LeanExpr::is_lambda(&value.unwrap()),
            "theorem value should be a lambda"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_declaration_name_extraction() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let ax_name = LeanName::from_str(lean, "TestExtract")?;
        let levels = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, ax_name, levels, prop, false)?;

        // Add to env and find it back using the extracted name
        let env = LeanEnvironment::empty(lean, 0)?;
        let env2 = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // Use LeanDeclaration::name to extract the name, then find with it
        let extracted_name = LeanDeclaration::name(&decl);
        let found = LeanEnvironment::find(&env2, &extracted_name)?;
        assert!(found.is_some(), "should find axiom using extracted name");

        Ok(())
    });
    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_duplicate_declaration_unchecked_fails() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Add axiom Y : Prop (unchecked)
        let name = LeanName::from_str(lean, "Y")?;
        let decl = LeanDeclaration::axiom(lean, name, LeanList::nil(lean)?, prop.clone(), false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // Try to add another axiom with the same name using unchecked add — should fail
        let name2 = LeanName::from_str(lean, "Y")?;
        let decl2 = LeanDeclaration::axiom(lean, name2, LeanList::nil(lean)?, prop, false)?;
        let result = LeanEnvironment::add_decl_unchecked(&env, &decl2);
        assert!(
            result.is_err(),
            "duplicate unchecked declaration should fail"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Adding and Querying Definitions ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_definition_and_query_kind() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // def myId : ∀ (P : Prop), P → P := λ P h, h
        let p_name = LeanName::from_str(lean, "P")?;
        let h_name = LeanName::from_str(lean, "h")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let inner_forall = LeanExpr::forall(h_name.clone(), bvar0, bvar1, BinderInfo::Default)?;
        let def_type = LeanExpr::forall(
            p_name.clone(),
            prop.clone(),
            inner_forall,
            BinderInfo::Default,
        )?;

        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0_inner = LeanExpr::bvar(lean, 0)?;
        let bvar0_body = LeanExpr::bvar(lean, 0)?;
        let inner_lambda = LeanExpr::lambda(h_name, bvar0_inner, bvar0_body, BinderInfo::Default)?;
        let value = LeanExpr::lambda(p_name, prop2, inner_lambda, BinderInfo::Default)?;

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
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "myId")?;
        let cinfo = LeanEnvironment::find(&new_env, &lookup)?.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Definition);
        assert!(LeanConstantInfo::has_value(&cinfo));

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Multiple Declarations in One Environment ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_find_nonexistent_in_populated_env() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // Add axiom A : Prop
        let a_name = LeanName::from_str(lean, "A")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let decl = LeanDeclaration::axiom(lean, a_name, LeanList::nil(lean)?, prop, false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // A should be findable
        let find_a = LeanName::from_str(lean, "A")?;
        assert!(LeanEnvironment::find(&env, &find_a)?.is_some(), "A missing");

        // Non-existent should still be None
        let find_d = LeanName::from_str(lean, "D")?;
        assert!(LeanEnvironment::find(&env, &find_d)?.is_none());

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Environment Immutability ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_environment_immutability() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Add axiom to get new_env
        let name = LeanName::from_str(lean, "myConst")?;
        let decl = LeanDeclaration::axiom(lean, name, LeanList::nil(lean)?, prop, false)?;
        let new_env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // Original env should NOT contain the new constant
        let lookup = LeanName::from_str(lean, "myConst")?;
        assert!(
            LeanEnvironment::find(&env, &lookup)?.is_none(),
            "original env should be unchanged"
        );

        // New env should contain it
        let lookup2 = LeanName::from_str(lean, "myConst")?;
        assert!(
            LeanEnvironment::find(&new_env, &lookup2)?.is_some(),
            "new env should contain the constant"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Error Cases ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_duplicate_declaration_fails() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        // Add axiom X : Prop (unchecked)
        let name = LeanName::from_str(lean, "X")?;
        let decl = LeanDeclaration::axiom(lean, name, LeanList::nil(lean)?, prop.clone(), false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        // Try to add another axiom with the same name using checked add — should fail
        let name2 = LeanName::from_str(lean, "X")?;
        let decl2 = LeanDeclaration::axiom(lean, name2, LeanList::nil(lean)?, prop, false)?;
        let result = LeanEnvironment::add_decl(&env, &decl2);
        assert!(result.is_err(), "duplicate declaration should fail");

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_add_ill_typed_theorem_fails() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // theorem bad : Prop := Prop  (ill-typed: Prop has type Type, not Prop)
        let name = LeanName::from_str(lean, "bad")?;
        let level_params = LeanList::nil(lean)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let proof = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let decl = LeanDeclaration::theorem(lean, name, level_params, prop, proof)?;

        let result = LeanEnvironment::add_decl(&env, &decl);
        assert!(result.is_err(), "ill-typed theorem should be rejected");

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ ConstantInfo Inspection ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_constant_info_name_roundtrip() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let name = LeanName::from_str(lean, "myConst")?;
        let decl = LeanDeclaration::axiom(lean, name.clone(), LeanList::nil(lean)?, prop, false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "myConst")?;
        let cinfo = LeanEnvironment::find(&env, &lookup)?.unwrap();
        let found_name = LeanConstantInfo::name(&cinfo)?;
        assert!(
            LeanName::eq(&found_name, &name),
            "constant name should round-trip"
        );

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_constant_info_level_params() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // axiom myAx.{u} : Sort u
        let u_name = LeanName::from_str(lean, "u")?;
        let u_level = LeanLevel::param(lean, u_name.clone())?;
        let sort_u = LeanExpr::sort(lean, u_level)?;

        let u_list_item = LeanList::cons(u_name.cast(), LeanList::nil(lean)?)?;

        let ax_name = LeanName::from_str(lean, "myAx")?;
        let decl = LeanDeclaration::axiom(lean, ax_name, u_list_item, sort_u, false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;

        let lookup = LeanName::from_str(lean, "myAx")?;
        let cinfo = LeanEnvironment::find(&env, &lookup)?.unwrap();
        let _level_params = LeanConstantInfo::level_params(&cinfo)?;
        // Just verify it doesn't crash — the level params list is valid

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Environment Trust Level ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_environment_different_trust_levels() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Trust level 0 = full checking
        let env0 = LeanEnvironment::empty(lean, 0)?;
        assert!(!env0.as_ptr().is_null());

        // Trust level 1 = skip some checks
        let env1 = LeanEnvironment::empty(lean, 1)?;
        assert!(!env1.as_ptr().is_null());

        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}

// ============ Module Loading Infrastructure ============

#[test]
fn test_module_struct_exists() {
    use leo3::module::LeanModule;

    // Verify the LeanModule type is available and can be referenced
    let _type_check =
        |path: &str, name: &str| -> Result<LeanModule, String> { LeanModule::load(path, name) };
}

#[test]
fn test_module_load_nonexistent_file_fails() {
    use leo3::module::LeanModule;

    let result = LeanModule::load("/nonexistent/path/libFoo.so", "Foo");
    assert!(result.is_err(), "loading nonexistent .so should fail");
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_lean_function_api() {
    leo3::prepare_freethreaded_lean();

    // The fact that this compiles proves the API is correctly structured.
    // Actual runtime testing would require a compiled Lean module.
}

// ============ External Objects ============

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore = "Requires Lean4 runtime")]
fn test_external_objects_in_module_context() {
    use leo3::external::{ExternalClass, LeanExternal};

    #[derive(Clone, Debug, PartialEq)]
    struct ModuleData {
        value: i32,
    }

    impl ExternalClass for ModuleData {
        fn class_name() -> &'static str {
            "ModuleData"
        }
    }

    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let data = ModuleData { value: 99 };
        let external = LeanExternal::new(lean, data)?;
        assert_eq!(external.get_ref().value, 99);
        Ok(())
    });

    assert!(result.is_ok(), "test failed: {:?}", result.err());
}
