//! Basic integration tests for meta-programming features

use leo3::meta::*;
use leo3::prelude::*;

#[test]
#[ignore = "Environment requires full IO initialization"]
fn test_environment_creation() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create an empty environment
        let env = LeanEnvironment::empty(lean, 0)?;

        // Should succeed
        assert!(!env.as_ptr().is_null());

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Environment creation failed: {:?}",
        result.err()
    );
}

#[test]
fn test_expression_bvar() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a bound variable
        let bvar0 = LeanExpr::bvar(lean, 0)?;

        // Check it's a bvar
        assert!(LeanExpr::is_bvar(&bvar0));
        assert!(!LeanExpr::is_app(&bvar0));

        // Extract index
        let idx = LeanExpr::bvar_idx(&bvar0)?;
        assert_eq!(idx, 0);

        Ok(())
    });

    assert!(result.is_ok(), "BVar test failed: {:?}", result.err());
}

#[test]
fn test_expression_sort() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create Prop (level zero)
        let level_zero = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, level_zero)?;

        // Check it's a sort
        assert!(LeanExpr::is_sort(&prop));

        // Create Type (level one)
        let level_one = LeanLevel::one(lean)?;
        let type0 = LeanExpr::sort(lean, level_one)?;

        assert!(LeanExpr::is_sort(&type0));

        Ok(())
    });

    assert!(result.is_ok(), "Sort test failed: {:?}", result.err());
}

#[test]
fn test_expression_const() {
    // TODO: This test requires proper Name construction using lean_name_mk_string
    // For now, skip creating consts until we implement Name FFI bindings
    let result: LeanResult<()> = leo3::test_with_lean(|_lean| Ok(()));

    assert!(result.is_ok(), "Const test failed: {:?}", result.err());
}

#[test]
fn test_expression_app() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create f and a as bound variables
        let f = LeanExpr::bvar(lean, 0)?;
        let a = LeanExpr::bvar(lean, 1)?;

        // Create application (f a)
        let app = LeanExpr::app(&f, &a)?;

        // Check it's an application
        assert!(LeanExpr::is_app(&app));

        // Extract function and argument
        let fn_expr = LeanExpr::app_fn(&app)?;
        let arg_expr = LeanExpr::app_arg(&app)?;

        assert!(LeanExpr::is_bvar(&fn_expr));
        assert!(LeanExpr::is_bvar(&arg_expr));

        assert_eq!(LeanExpr::bvar_idx(&fn_expr)?, 0);
        assert_eq!(LeanExpr::bvar_idx(&arg_expr)?, 1);

        Ok(())
    });

    assert!(result.is_ok(), "App test failed: {:?}", result.err());
}

#[test]
fn test_expression_lambda() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create λ x : Prop, x
        let x_name = LeanString::mk(lean, "x")?;
        let prop_level = LeanLevel::zero(lean)?;
        let prop_sort = LeanExpr::sort(lean, prop_level)?;
        let x_body = LeanExpr::bvar(lean, 0)?;

        let lambda = LeanExpr::lambda(x_name.clone(), prop_sort, x_body, BinderInfo::Default)?;

        // Check it's a lambda
        assert!(LeanExpr::is_lambda(&lambda));

        // Extract parts
        let name = LeanExpr::lambda_name(&lambda)?;
        let name_str = LeanString::cstr(&name)?.to_string();
        assert_eq!(name_str, "x");

        let binder_type = LeanExpr::lambda_type(&lambda)?;
        assert!(LeanExpr::is_sort(&binder_type));

        let body = LeanExpr::lambda_body(&lambda)?;
        assert!(LeanExpr::is_bvar(&body));

        let info = LeanExpr::lambda_info(&lambda)?;
        assert_eq!(info, BinderInfo::Default);

        Ok(())
    });

    assert!(result.is_ok(), "Lambda test failed: {:?}", result.err());
}

#[test]
fn test_expression_forall() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create ∀ (n : Prop), Prop
        let n_name = LeanString::mk(lean, "n")?;
        let prop_level = LeanLevel::zero(lean)?;
        let prop_sort = LeanExpr::sort(lean, prop_level.clone())?;
        let prop_body = LeanExpr::sort(lean, prop_level)?;

        let forall = LeanExpr::forall(n_name, prop_sort, prop_body, BinderInfo::Default)?;

        // Check it's a forall
        assert!(LeanExpr::is_forall(&forall));

        // Extract domain
        let domain = LeanExpr::forall_domain(&forall)?;
        assert!(LeanExpr::is_sort(&domain));

        Ok(())
    });

    assert!(result.is_ok(), "Forall test failed: {:?}", result.err());
}

#[test]
fn test_expression_arrow() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create Prop → Prop
        let prop_level = LeanLevel::zero(lean)?;
        let prop1 = LeanExpr::sort(lean, prop_level.clone())?;
        let prop2 = LeanExpr::sort(lean, prop_level)?;

        let arrow = LeanExpr::arrow(prop1, prop2)?;

        // Arrow is a forall
        assert!(LeanExpr::is_forall(&arrow));

        // And it is a non-dependent arrow
        assert!(LeanExpr::is_arrow(&arrow));

        Ok(())
    });

    assert!(result.is_ok(), "Arrow test failed: {:?}", result.err());
}

#[test]
fn test_expression_literal() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create literal 42
        let lit = LeanLiteral::nat(lean, 42)?;
        let expr = LeanExpr::lit(lean, lit)?;

        // Check it's a literal
        assert!(LeanExpr::is_lit(&expr));

        Ok(())
    });

    assert!(result.is_ok(), "Literal test failed: {:?}", result.err());
}

#[test]
fn test_expression_dbg_string() {
    // TODO: dbg_to_string requires Lean's print system to be initialized
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a bound variable
        let _bvar = LeanExpr::bvar(lean, 0)?;
        // Skip dbg_to_string for now as it requires IO initialization

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Debug string test failed: {:?}",
        result.err()
    );
}

#[test]
fn test_expression_alpha_eqv() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create λ x, x
        let x_name = LeanString::mk(lean, "x")?;
        let prop_level = LeanLevel::zero(lean)?;
        let prop_sort = LeanExpr::sort(lean, prop_level.clone())?;
        let x_body = LeanExpr::bvar(lean, 0)?;

        let lambda_x = LeanExpr::lambda(
            x_name,
            prop_sort.clone(),
            x_body.clone(),
            BinderInfo::Default,
        )?;

        // Create λ y, y
        let y_name = LeanString::mk(lean, "y")?;
        let lambda_y = LeanExpr::lambda(y_name, prop_sort, x_body, BinderInfo::Default)?;

        // They should be alpha equivalent
        assert!(LeanExpr::alpha_eqv(&lambda_x, &lambda_y));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Alpha equivalence test failed: {:?}",
        result.err()
    );
}

#[test]
fn test_expression_mk_app() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a function f
        let f = LeanExpr::bvar(lean, 0)?;

        // Create arguments a, b, c
        let a = LeanExpr::bvar(lean, 1)?;
        let b = LeanExpr::bvar(lean, 2)?;
        let c = LeanExpr::bvar(lean, 3)?;

        // Create f a b c
        let app = LeanExpr::mk_app(&f, &[&a, &b, &c])?;

        // Should be an application
        assert!(LeanExpr::is_app(&app));

        // The outermost application should have c as argument
        let arg = LeanExpr::app_arg(&app)?;
        assert_eq!(LeanExpr::bvar_idx(&arg)?, 3);

        Ok(())
    });

    assert!(result.is_ok(), "mk_app test failed: {:?}", result.err());
}

#[test]
fn test_level_operations() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create levels
        let _zero = LeanLevel::zero(lean)?;
        let one = LeanLevel::one(lean)?;
        let two = LeanLevel::succ(one.clone())?;

        // Create max
        let _max_level = LeanLevel::max(one.clone(), two.clone())?;

        // Create imax
        let _imax_level = LeanLevel::imax(one, two)?;

        // Create param
        let u_name = LeanString::mk(lean, "u")?;
        let _param_level = LeanLevel::param(lean, u_name)?;

        // All operations should succeed
        Ok(())
    });

    assert!(
        result.is_ok(),
        "Level operations test failed: {:?}",
        result.err()
    );
}
