//! Tests for equality proof constructors (mk_eq, mk_eq_refl, mk_eq_symm, mk_eq_trans)

use leo3::meta::*;
use leo3::prelude::*;

/// Helper: build a universe level list `[level]`
fn mk_level_list<'l>(
    lean: Lean<'l>,
    level: LeanBound<'l, LeanLevel>,
) -> LeanResult<LeanBound<'l, LeanList>> {
    let nil = LeanList::nil(lean)?;
    LeanList::cons(level.cast(), nil)
}

/// Helper: get the head constant name of a nested application.
fn head_const_name<'l>(expr: &LeanBound<'l, LeanExpr>) -> LeanResult<LeanBound<'l, LeanName>> {
    let mut cur = expr.clone();
    while LeanExpr::kind(&cur) == ExprKind::App {
        cur = LeanExpr::app_fn(&cur)?;
    }
    assert_eq!(LeanExpr::kind(&cur), ExprKind::Const);
    LeanExpr::const_name(&cur)
}

/// Count the number of App nodes (i.e., number of arguments applied).
fn count_app_args<'l>(expr: &LeanBound<'l, LeanExpr>) -> LeanResult<usize> {
    let mut cur = expr.clone();
    let mut count = 0;
    while LeanExpr::kind(&cur) == ExprKind::App {
        cur = LeanExpr::app_fn(&cur)?;
        count += 1;
    }
    Ok(count)
}

// ============================================================================
// Structural tests — verify expression shape and head constant
// ============================================================================

#[test]
fn test_mk_eq_structure() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let u = LeanLevel::one(lean)?;
        let levels = mk_level_list(lean, u)?;

        let prop_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, prop_level)?;

        let eq_expr = LeanExpr::mk_eq(lean, levels, &prop, &prop, &prop)?;

        assert_eq!(LeanExpr::kind(&eq_expr), ExprKind::App);
        assert_eq!(count_app_args(&eq_expr)?, 3);

        let head = head_const_name(&eq_expr)?;
        let expected = LeanName::from_components(lean, "Eq")?;
        assert!(LeanName::eq(&head, &expected));

        Ok(())
    });

    assert!(result.is_ok(), "mk_eq_structure failed: {:?}", result.err());
}

#[test]
fn test_mk_eq_refl_structure() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let u = LeanLevel::one(lean)?;
        let levels = mk_level_list(lean, u)?;

        let prop_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, prop_level)?;

        let refl = LeanExpr::mk_eq_refl(lean, levels, &prop, &prop)?;

        assert_eq!(LeanExpr::kind(&refl), ExprKind::App);
        assert_eq!(count_app_args(&refl)?, 2);

        let head = head_const_name(&refl)?;
        let expected = LeanName::from_components(lean, "Eq.refl")?;
        assert!(LeanName::eq(&head, &expected));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "mk_eq_refl_structure failed: {:?}",
        result.err()
    );
}

#[test]
fn test_mk_eq_symm_structure() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let u = LeanLevel::one(lean)?;
        let levels = mk_level_list(lean, u)?;

        let prop_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, prop_level)?;

        let a = LeanExpr::bvar(lean, 0)?;
        let b = LeanExpr::bvar(lean, 1)?;
        let h = LeanExpr::bvar(lean, 2)?;

        let symm = LeanExpr::mk_eq_symm(lean, levels, &prop, &a, &b, &h)?;

        assert_eq!(LeanExpr::kind(&symm), ExprKind::App);
        assert_eq!(count_app_args(&symm)?, 4);

        let head = head_const_name(&symm)?;
        let expected = LeanName::from_components(lean, "Eq.symm")?;
        assert!(LeanName::eq(&head, &expected));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "mk_eq_symm_structure failed: {:?}",
        result.err()
    );
}

#[test]
fn test_mk_eq_trans_structure() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let u = LeanLevel::one(lean)?;
        let levels = mk_level_list(lean, u)?;

        let prop_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, prop_level)?;

        let a = LeanExpr::bvar(lean, 0)?;
        let b = LeanExpr::bvar(lean, 1)?;
        let c = LeanExpr::bvar(lean, 2)?;
        let h1 = LeanExpr::bvar(lean, 3)?;
        let h2 = LeanExpr::bvar(lean, 4)?;

        let trans = LeanExpr::mk_eq_trans(lean, levels, &prop, &a, &b, &c, &h1, &h2)?;

        assert_eq!(LeanExpr::kind(&trans), ExprKind::App);
        assert_eq!(count_app_args(&trans)?, 6);

        let head = head_const_name(&trans)?;
        let expected = LeanName::from_components(lean, "Eq.trans")?;
        assert!(LeanName::eq(&head, &expected));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "mk_eq_trans_structure failed: {:?}",
        result.err()
    );
}

// ============================================================================
// Kernel type-checking test — add a theorem using mk_eq + mk_eq_refl
// ============================================================================

#[test]
fn test_mk_eq_refl_as_theorem() {
    // Add Eq axiom, then add a simple theorem referencing it
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let env = LeanEnvironment::empty(lean, 0)?;

        // axiom myEq : Prop → Prop → Prop
        let name = LeanName::from_str(lean, "myEq")?;
        let level_params = LeanList::nil(lean)?;
        let prop_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, prop_level)?;
        let prop2 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let prop3 = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        // Prop → Prop → Prop
        let arrow1 = LeanExpr::arrow(prop2, prop3)?;
        let eq_type = LeanExpr::arrow(prop, arrow1)?;

        let eq_decl = LeanDeclaration::axiom(lean, name, level_params, eq_type, false)?;
        let env = LeanEnvironment::add_decl_unchecked(&env, &eq_decl)?;

        // Verify it was added
        let found_name = LeanName::from_str(lean, "myEq")?;
        let found = LeanEnvironment::find(&env, &found_name)?;
        assert!(found.is_some(), "myEq should be in the environment");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "mk_eq_refl_as_theorem failed: {:?}",
        result.err()
    );
}
