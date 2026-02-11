//! Prelude environment integration tests
//!
//! These tests exercise working with prelude-like types (Nat, String, List, etc.)
//! by constructing environments that contain axiomatized versions of core types,
//! looking up constants, and building complex type expressions.
//!
//! Since `LeanEnvironment::empty()` does not include the Lean prelude, we
//! simulate prelude types by adding axioms for Nat, String, List, etc.

use leo3::meta::*;
use leo3::prelude::*;

// ============================================================================
// Helpers
// ============================================================================

/// Add a simple type axiom (e.g., `axiom Nat : Type`) to the environment.
fn add_type_axiom<'l>(
    env: &LeanBound<'l, LeanEnvironment>,
    lean: Lean<'l>,
    name_str: &str,
) -> LeanResult<LeanBound<'l, LeanEnvironment>> {
    let name = LeanName::from_components(lean, name_str)?;
    let level_params = LeanList::nil(lean)?;
    let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
    let decl = LeanDeclaration::axiom(lean, name, level_params, type0, false)?;
    LeanEnvironment::add_decl_unchecked(env, &decl)
}

/// Add a universe-polymorphic type constructor axiom.
fn add_poly_type_axiom<'l>(
    env: &LeanBound<'l, LeanEnvironment>,
    lean: Lean<'l>,
    name_str: &str,
) -> LeanResult<LeanBound<'l, LeanEnvironment>> {
    let name = LeanName::from_components(lean, name_str)?;
    let u_name = LeanName::from_str(lean, "u")?;
    let u_level = LeanLevel::param(lean, u_name.clone())?;
    let u_succ = LeanLevel::succ(u_level)?;
    let sort_u1_dom = LeanExpr::sort(lean, u_succ.clone())?;
    let sort_u1_cod = LeanExpr::sort(lean, u_succ)?;
    let ty = LeanExpr::arrow(sort_u1_dom, sort_u1_cod)?;
    let level_params = LeanList::cons(u_name.cast(), LeanList::nil(lean)?)?;
    let decl = LeanDeclaration::axiom(lean, name, level_params, ty, false)?;
    LeanEnvironment::add_decl_unchecked(env, &decl)
}

/// Build an environment with axiomatized prelude types.
fn build_prelude_env<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, LeanEnvironment>> {
    let env = LeanEnvironment::empty(lean, 0)?;
    let env = add_type_axiom(&env, lean, "Nat")?;
    let env = add_type_axiom(&env, lean, "String")?;
    let env = add_type_axiom(&env, lean, "Bool")?;
    let env = add_type_axiom(&env, lean, "Int")?;
    let env = add_poly_type_axiom(&env, lean, "List")?;
    let env = add_poly_type_axiom(&env, lean, "Array")?;
    add_poly_type_axiom(&env, lean, "Option")
}

// ============================================================================
// Building prelude environments
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_build_prelude_env_succeeds() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let _env = build_prelude_env(lean)?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_add_multiple_simple_axioms() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let env = add_type_axiom(&env, lean, "Nat")?;
        let env = add_type_axiom(&env, lean, "String")?;
        let env = add_type_axiom(&env, lean, "Bool")?;
        let _env = add_type_axiom(&env, lean, "Int")?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_add_polymorphic_axiom() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let _env = add_poly_type_axiom(&env, lean, "List")?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_add_distinct_axioms_to_same_env() {
    // Verify we can add multiple distinct axioms to the same base environment
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let env = add_type_axiom(&env, lean, "Foo")?;
        let _env = add_type_axiom(&env, lean, "Bar")?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Looking up constants (one find per test)
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_nat_exists() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Nat")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(found.is_some(), "Nat should be found");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_nat_is_axiom() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Nat")?;
        let cinfo = LeanEnvironment::find(&env, &name)?.unwrap();
        assert_eq!(LeanConstantInfo::kind(&cinfo), ConstantKind::Axiom);
        assert!(!LeanConstantInfo::has_value(&cinfo));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_nat_type_is_sort() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Nat")?;
        let cinfo = LeanEnvironment::find(&env, &name)?.unwrap();
        let ty = LeanConstantInfo::type_(&cinfo)?;
        assert!(LeanExpr::is_sort(&ty), "Nat's type should be Sort");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_list_type_is_arrow() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "List")?;
        let cinfo = LeanEnvironment::find(&env, &name)?.unwrap();
        let ty = LeanConstantInfo::type_(&cinfo)?;
        assert!(
            LeanExpr::is_forall(&ty),
            "List's type should be Forall (arrow)"
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_nonexistent_constant_not_found() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Float")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(found.is_none(), "Float should not exist");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_option_exists() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Option")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(found.is_some(), "Option should be found");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_lookup_array_exists() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "Array")?;
        let found = LeanEnvironment::find(&env, &name)?;
        assert!(found.is_some(), "Array should be found");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Adding declarations with prelude-like types
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_add_axiom_referencing_prelude_type() {
    // axiom myNatFn : Nat → Nat (using const refs to Nat)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "myNatFn")?;
        let nat_name1 = LeanName::from_str(lean, "Nat")?;
        let nat1 = LeanExpr::const_(lean, nat_name1, LeanList::nil(lean)?)?;
        let nat_name2 = LeanName::from_str(lean, "Nat")?;
        let nat2 = LeanExpr::const_(lean, nat_name2, LeanList::nil(lean)?)?;
        let nat_to_nat = LeanExpr::arrow(nat1, nat2)?;
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::axiom(lean, name.clone(), level_params, nat_to_nat, false)?;
        let new_env = LeanEnvironment::add_decl_unchecked(&env, &decl)?;
        let found = LeanEnvironment::find(&new_env, &name)?;
        assert!(found.is_some());
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_add_definition_with_kernel_check() {
    // def natId : Nat → Nat := λ n, n  (kernel-checked via add_decl)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = build_prelude_env(lean)?;
        let name = LeanName::from_str(lean, "natId")?;
        let n_name = LeanName::from_str(lean, "n")?;
        let nat_name1 = LeanName::from_str(lean, "Nat")?;
        let nat1 = LeanExpr::const_(lean, nat_name1, LeanList::nil(lean)?)?;
        let nat_name2 = LeanName::from_str(lean, "Nat")?;
        let nat2 = LeanExpr::const_(lean, nat_name2, LeanList::nil(lean)?)?;
        let fn_type = LeanExpr::arrow(nat1, nat2)?;
        let nat_name3 = LeanName::from_str(lean, "Nat")?;
        let nat3 = LeanExpr::const_(lean, nat_name3, LeanList::nil(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let value = LeanExpr::lambda(n_name, nat3, body, BinderInfo::Default)?;
        let hints = unsafe { LeanBound::from_owned_ptr(lean, leo3_ffi::lean_box(0)) };
        let level_params = LeanList::nil(lean)?;
        let decl = LeanDeclaration::definition(
            lean,
            name.clone(),
            level_params,
            fn_type,
            value,
            hints,
            DefinitionSafety::Safe,
        )?;
        let new_env = LeanEnvironment::add_decl(&env, &decl)?;
        let found = LeanEnvironment::find(&new_env, &name)?;
        assert!(found.is_some());
        assert_eq!(
            LeanConstantInfo::kind(&found.unwrap()),
            ConstantKind::Definition
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// MetaM operations on prelude-like expressions (using empty env)
//
// Note: MetaMContext currently only works with empty environments.
// These tests construct prelude-like type expressions using sorts, lambdas,
// and foralls to exercise MetaM operations.
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_check_arrow_sort_to_sort() {
    // Type → Type should be well-typed
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let type1 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let type2 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let arrow = LeanExpr::arrow(type1, type2)?;
        ctx.check(&arrow)?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_check_forall_type_to_prop() {
    // ∀ (A : Type), Prop  should be well-typed
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let a_name = LeanName::from_str(lean, "A")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let forall_expr = LeanExpr::forall(a_name, type0, prop, BinderInfo::Default)?;
        ctx.check(&forall_expr)?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_infer_type_of_sort() {
    // Type : Type 1
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let ty = ctx.infer_type(&type0)?;
        assert!(LeanExpr::is_sort(&ty), "Type of Type should be a Sort");
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_is_def_eq_same_sort() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let type1 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let type2 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        assert!(ctx.is_def_eq(&type1, &type2)?);
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_is_def_eq_different_sorts() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        assert!(!ctx.is_def_eq(&prop, &type0)?);
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_whnf_let_reduces() {
    // let x : Type := Prop in x  should reduce to Prop
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let x_name = LeanName::from_str(lean, "x")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let let_expr = LeanExpr::let_(x_name, type0, prop, body, false)?;
        let whnf = ctx.whnf(&let_expr)?;
        assert!(
            LeanExpr::is_sort(&whnf),
            "whnf of (let x := Prop in x) should be Sort"
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_whnf_beta_reduces() {
    // (λ (T : Type 1), T) Type  should reduce to Type
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let t_name = LeanName::from_str(lean, "T")?;
        let type1 = LeanExpr::sort(lean, LeanLevel::succ(LeanLevel::one(lean)?)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(t_name, type1, body, BinderInfo::Default)?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let app = LeanExpr::app(&lambda, &type0)?;
        let whnf = ctx.whnf(&app)?;
        assert!(
            LeanExpr::is_sort(&whnf),
            "whnf of ((λ T, T) Type) should be Sort"
        );
        // Verify it's Type (Sort 1)
        let type0_again = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        assert!(ctx.is_def_eq(&whnf, &type0_again)?);
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_dependent_type() {
    // ∀ (A : Type), A → A  should be well-typed
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let a_name = LeanName::from_str(lean, "A")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;
        let underscore = LeanName::from_str(lean, "_")?;
        let domain = LeanExpr::bvar(lean, 0)?;
        let codomain = LeanExpr::bvar(lean, 1)?;
        let a_to_a = LeanExpr::forall(underscore, domain, codomain, BinderInfo::Default)?;
        let forall_expr = LeanExpr::forall(a_name, type0, a_to_a, BinderInfo::Default)?;
        ctx.check(&forall_expr)?;
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_metam_is_prop_on_prop() {
    // Prop (Sort 0) should be a proposition... well, its type is Type (Sort 1),
    // which is not Prop. But True : Prop would be a proposition.
    // Let's test that Sort 0 is not a proposition (its type is Sort 1, not Sort 0).
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;
        let mut ctx = MetaMContext::new(lean, env)?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        assert!(
            !ctx.is_prop(&prop)?,
            "Prop itself is not a proposition (its type is Type)"
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Expression construction with prelude-like types
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_const_expression() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        assert!(LeanExpr::is_const(&nat));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_polymorphic_const_expression() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let list_name = LeanName::from_str(lean, "List")?;
        let level = LeanLevel::one(lean)?;
        let levels = LeanList::cons(level.cast(), LeanList::nil(lean)?)?;
        let list = LeanExpr::const_(lean, list_name, levels)?;
        assert!(LeanExpr::is_const(&list));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_applied_type_expression() {
    // List.{1} Nat  (as expression, no type checking)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        let list_name = LeanName::from_str(lean, "List")?;
        let level = LeanLevel::one(lean)?;
        let levels = LeanList::cons(level.cast(), LeanList::nil(lean)?)?;
        let list = LeanExpr::const_(lean, list_name, levels)?;
        let list_nat = LeanExpr::app(&list, &nat)?;
        assert!(LeanExpr::is_app(&list_nat));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_nested_applied_type() {
    // Option.{1} (List.{1} Nat)
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        let list_name = LeanName::from_str(lean, "List")?;
        let l1 = LeanLevel::one(lean)?;
        let levels1 = LeanList::cons(l1.cast(), LeanList::nil(lean)?)?;
        let list = LeanExpr::const_(lean, list_name, levels1)?;
        let list_nat = LeanExpr::app(&list, &nat)?;
        let option_name = LeanName::from_str(lean, "Option")?;
        let l2 = LeanLevel::one(lean)?;
        let levels2 = LeanList::cons(l2.cast(), LeanList::nil(lean)?)?;
        let option = LeanExpr::const_(lean, option_name, levels2)?;
        let option_list_nat = LeanExpr::app(&option, &list_nat)?;
        assert!(LeanExpr::is_app(&option_list_nat));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_arrow_between_consts() {
    // Nat → String  as expression
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        let str_name = LeanName::from_str(lean, "String")?;
        let string = LeanExpr::const_(lean, str_name, LeanList::nil(lean)?)?;
        let arrow = LeanExpr::arrow(nat, string)?;
        assert!(LeanExpr::is_forall(&arrow));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_construct_lambda_with_const_type() {
    // λ (x : Nat), x
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let x_name = LeanName::from_str(lean, "x")?;
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, nat, body, BinderInfo::Default)?;
        assert!(LeanExpr::is_lambda(&lambda));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_expr_equality_same_const() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat1_name = LeanName::from_str(lean, "Nat")?;
        let nat1 = LeanExpr::const_(lean, nat1_name, LeanList::nil(lean)?)?;
        let nat2_name = LeanName::from_str(lean, "Nat")?;
        let nat2 = LeanExpr::const_(lean, nat2_name, LeanList::nil(lean)?)?;
        assert!(LeanExpr::equal(&nat1, &nat2));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_expr_equality_different_consts() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        let str_name = LeanName::from_str(lean, "String")?;
        let string = LeanExpr::const_(lean, str_name, LeanList::nil(lean)?)?;
        assert!(!LeanExpr::equal(&nat, &string));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

// ============================================================================
// Literal types
// ============================================================================

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_nat_literal_type_is_const() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_lit = LeanLiteral::nat(lean, 42)?;
        let lit_type = LeanLiteral::type_(&nat_lit)?;
        assert!(
            LeanExpr::is_const(&lit_type),
            "Nat literal type should be a const"
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_string_literal_type_is_const() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let str_lit = LeanLiteral::string(lean, "hello")?;
        let lit_type = LeanLiteral::type_(&str_lit)?;
        assert!(
            LeanExpr::is_const(&lit_type),
            "String literal type should be a const"
        );
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_nat_and_string_literal_types_differ() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_lit = LeanLiteral::nat(lean, 0)?;
        let str_lit = LeanLiteral::string(lean, "")?;
        let nat_type = LeanLiteral::type_(&nat_lit)?;
        let str_type = LeanLiteral::type_(&str_lit)?;
        assert!(!LeanExpr::equal(&nat_type, &str_type));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_nat_literal_type_matches_nat_const() {
    // The type of a Nat literal should be the @Nat constant
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let nat_lit = LeanLiteral::nat(lean, 100)?;
        let lit_type = LeanLiteral::type_(&nat_lit)?;
        let nat_name = LeanName::from_str(lean, "Nat")?;
        let nat_const = LeanExpr::const_(lean, nat_name, LeanList::nil(lean)?)?;
        assert!(LeanExpr::equal(&lit_type, &nat_const));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(not(feature = "runtime-tests"), ignore)]
fn test_string_literal_type_matches_string_const() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let str_lit = LeanLiteral::string(lean, "world")?;
        let lit_type = LeanLiteral::type_(&str_lit)?;
        let str_name = LeanName::from_str(lean, "String")?;
        let str_const = LeanExpr::const_(lean, str_name, LeanList::nil(lean)?)?;
        assert!(LeanExpr::equal(&lit_type, &str_const));
        Ok(())
    });
    assert!(result.is_ok(), "Test failed: {:?}", result.err());
}
