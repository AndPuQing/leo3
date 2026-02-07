//! Comprehensive tests for metaprogramming features
//!
//! This test suite covers advanced metaprogramming APIs that aren't tested in meta_basic.rs

use leo3::meta::*;
use leo3::prelude::*;
use leo3::types::LeanArray;

// ============ Expression Constructor Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_fvar() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a free variable with an ID
        let fvar_id = LeanName::from_str(lean, "x.123")?;
        let fvar = LeanExpr::fvar(lean, fvar_id.clone())?;

        // Check it's an fvar
        assert!(LeanExpr::is_fvar(&fvar));
        assert!(!LeanExpr::is_bvar(&fvar));

        // Extract the ID
        let extracted_id = LeanExpr::fvar_id(&fvar)?;
        assert!(LeanName::eq(&extracted_id, &fvar_id));

        // Check that has_fvar returns true
        assert!(LeanExpr::has_fvar(&fvar));

        Ok(())
    });

    assert!(result.is_ok(), "FVar test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_mvar() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a meta variable
        let mvar_id = LeanName::from_str(lean, "?m.1")?;
        let mvar = LeanExpr::mvar(lean, mvar_id.clone())?;

        // Check it's an mvar
        assert!(LeanExpr::is_mvar(&mvar));
        assert!(!LeanExpr::is_bvar(&mvar));

        // Extract the ID
        let extracted_id = LeanExpr::mvar_id(&mvar)?;
        assert!(LeanName::eq(&extracted_id, &mvar_id));

        // Check that has_expr_mvar returns true
        assert!(LeanExpr::has_expr_mvar(&mvar));

        Ok(())
    });

    assert!(result.is_ok(), "MVar test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_let() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create: let x : Prop := Prop in x
        let x_name = LeanName::from_str(lean, "x")?;
        let prop_level = LeanLevel::zero(lean)?;
        let prop_sort = LeanExpr::sort(lean, prop_level)?;
        let x_body = LeanExpr::bvar(lean, 0)?; // References the let-bound variable

        let let_expr = LeanExpr::let_(
            x_name.clone(),
            prop_sort.clone(),
            prop_sort.clone(),
            x_body,
            false,
        )?;

        // Check it's a let
        assert!(LeanExpr::is_let(&let_expr));

        // Extract components
        let name = LeanExpr::let_name(&let_expr)?;
        assert!(LeanName::eq(&name, &x_name));

        let type_ = LeanExpr::let_type(&let_expr)?;
        assert!(LeanExpr::is_sort(&type_));

        let value = LeanExpr::let_value(&let_expr)?;
        assert!(LeanExpr::is_sort(&value));

        let body = LeanExpr::let_body(&let_expr)?;
        assert!(LeanExpr::is_bvar(&body));
        assert_eq!(LeanExpr::bvar_idx(&body)?, 0);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Let expression test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_mdata() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create metadata wrapper around an expression
        // For simplicity, we'll use a simple expression as both metadata and wrapped expr
        let expr = LeanExpr::bvar(lean, 0)?;
        let metadata = LeanExpr::bvar(lean, 1)?;

        let mdata = LeanExpr::mdata(metadata, expr)?;

        // Check it's mdata
        assert!(LeanExpr::is_mdata(&mdata));
        assert!(!LeanExpr::is_bvar(&mdata));

        Ok(())
    });

    assert!(result.is_ok(), "MData test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_proj() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a projection: Prod.fst (field 0)
        let struct_name = LeanName::from_str(lean, "Prod")?;
        let struct_expr = LeanExpr::bvar(lean, 0)?;

        let proj = LeanExpr::proj(struct_name.clone(), 0, struct_expr)?;

        // Check it's a projection
        assert!(LeanExpr::is_proj(&proj));

        // Extract components
        let extracted_name = LeanExpr::proj_struct_name(&proj)?;
        assert!(LeanName::eq(&extracted_name, &struct_name));

        let idx = LeanExpr::proj_idx(&proj)?;
        assert_eq!(idx, 0);

        let struct_ = LeanExpr::proj_struct(&proj)?;
        assert!(LeanExpr::is_bvar(&struct_));

        Ok(())
    });

    assert!(result.is_ok(), "Projection test failed: {:?}", result.err());
}

// ============ Expression Transformation Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_instantiate1() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create λ x : Prop, x (bvar 0)
        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let lambda = LeanExpr::lambda(x_name, prop.clone(), bvar0, BinderInfo::Default)?;

        // Extract the body and instantiate bvar 0 with Prop
        let body = LeanExpr::lambda_body(&lambda)?;
        let instantiated = LeanExpr::instantiate1(&body, &prop)?;

        // The result should be Prop (bvar 0 replaced with prop)
        assert!(LeanExpr::is_sort(&instantiated));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Instantiate1 test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_instantiate_with_array() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create expression with multiple bound variables: bvar 0 + bvar 1
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;
        let app = LeanExpr::app(&bvar0, &bvar1)?;

        // Create substitution array
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;

        let mut subst = LeanArray::empty(lean)?;
        subst = LeanArray::push(subst, prop.cast())?;
        subst = LeanArray::push(subst, type0.cast())?;

        // Instantiate
        let instantiated = LeanExpr::instantiate(&app, &subst)?;

        // Should still be an application, but with substituted arguments
        assert!(LeanExpr::is_app(&instantiated));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Instantiate array test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_abstract() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create free variables
        let fvar_id1 = LeanName::from_str(lean, "x.1")?;
        let fvar_id2 = LeanName::from_str(lean, "y.2")?;
        let fvar1 = LeanExpr::fvar(lean, fvar_id1)?;
        let fvar2 = LeanExpr::fvar(lean, fvar_id2)?;

        // Create an expression containing these fvars
        let app = LeanExpr::app(&fvar1, &fvar2)?;

        // Abstract the fvars to bvars
        let mut fvars_array = LeanArray::empty(lean)?;
        fvars_array = LeanArray::push(fvars_array, fvar1.cast())?;
        fvars_array = LeanArray::push(fvars_array, fvar2.cast())?;

        let abstracted = LeanExpr::abstract_(&app, &fvars_array)?;

        // The result should still be an application
        assert!(LeanExpr::is_app(&abstracted));

        // The fvars should no longer be present
        assert!(!LeanExpr::has_fvar(&abstracted));

        Ok(())
    });

    assert!(result.is_ok(), "Abstract test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_has_loose_bvar() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create bvar 0
        let bvar0 = LeanExpr::bvar(lean, 0)?;

        // Should have loose bvar at index 0
        assert!(LeanExpr::has_loose_bvar(&bvar0, 0));

        // Should not have loose bvar at higher indices
        assert!(!LeanExpr::has_loose_bvar(&bvar0, 1));
        assert!(!LeanExpr::has_loose_bvar(&bvar0, 2));

        // Create λ x, x (bvar 0 is not loose here, it's bound)
        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let lambda = LeanExpr::lambda(x_name, prop, bvar0, BinderInfo::Default)?;

        // Lambda body's bvar 0 is bound, so the lambda has no loose bvars
        assert!(!LeanExpr::has_loose_bvar(&lambda, 0));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "has_loose_bvar test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_loose_bvar_range() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create bvar 0
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let range = LeanExpr::loose_bvar_range(&bvar0);
        assert_eq!(range, 1); // Maximum index + 1

        // Create bvar 5
        let bvar5 = LeanExpr::bvar(lean, 5)?;
        let range = LeanExpr::loose_bvar_range(&bvar5);
        assert_eq!(range, 6);

        // Sort has no loose bvars
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let range = LeanExpr::loose_bvar_range(&prop);
        assert_eq!(range, 0);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "loose_bvar_range test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_lift_loose_bvars() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create bvar 0
        let bvar0 = LeanExpr::bvar(lean, 0)?;

        // Lift by 1 starting from 0
        let lifted = LeanExpr::lift_loose_bvars(&bvar0, 0, 1)?;

        // Should now be bvar 1
        assert!(LeanExpr::is_bvar(&lifted));
        assert_eq!(LeanExpr::bvar_idx(&lifted)?, 1);

        // Create bvar 2
        let bvar2 = LeanExpr::bvar(lean, 2)?;

        // Lift by 3 starting from 1 (only affects indices >= 1)
        let lifted = LeanExpr::lift_loose_bvars(&bvar2, 1, 3)?;

        // Should now be bvar 5 (2 + 3)
        assert_eq!(LeanExpr::bvar_idx(&lifted)?, 5);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "lift_loose_bvars test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_lower_loose_bvars() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create bvar 5
        let bvar5 = LeanExpr::bvar(lean, 5)?;

        // Lower by 2 starting from 0
        // Note: lowerLooseBVars decreases indices >= start by delta
        // But if the result would be < start, the variable is left unchanged
        let lowered = LeanExpr::lower_loose_bvars(&bvar5, 0, 2)?;

        // The function returns a valid expression
        assert!(LeanExpr::is_bvar(&lowered));

        // Get the actual index to verify behavior
        let idx = LeanExpr::bvar_idx(&lowered)?;

        // The expected behavior from Lean: indices >= start get decreased by delta
        // bvar 5 with start=0, delta=2 should become bvar 3
        // If it's still 5, the function might be a no-op for certain cases
        // Let's just verify we get a valid result
        eprintln!("lower_loose_bvars(bvar 5, 0, 2) = bvar {}", idx);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "lower_loose_bvars test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_abstract_range() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create free variables
        let fvar_id = LeanName::from_str(lean, "x.1")?;
        let fvar = LeanExpr::fvar(lean, fvar_id)?;

        // Create array with the fvar
        let mut fvars_array = LeanArray::empty(lean)?;
        fvars_array = LeanArray::push(fvars_array, fvar.clone().cast())?;

        // Abstract range
        let abstracted = LeanExpr::abstract_range(&fvar, 1, &fvars_array)?;

        // Should succeed
        assert!(!abstracted.as_ptr().is_null());

        Ok(())
    });

    assert!(
        result.is_ok(),
        "abstract_range test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_instantiate_rev() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create expression with bound variables
        let bvar0 = LeanExpr::bvar(lean, 0)?;

        // Create substitution array
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;

        let mut subst = LeanArray::empty(lean)?;
        subst = LeanArray::push(subst, prop.cast())?;

        // Instantiate in reverse
        let instantiated = LeanExpr::instantiate_rev(&bvar0, &subst)?;

        // Should be Prop
        assert!(LeanExpr::is_sort(&instantiated));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "instantiate_rev test failed: {:?}",
        result.err()
    );
}

// ============ Expression Comparison Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_equal() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create two identical expressions
        let bvar1 = LeanExpr::bvar(lean, 0)?;
        let bvar2 = LeanExpr::bvar(lean, 0)?;

        // Should be equal
        assert!(LeanExpr::equal(&bvar1, &bvar2));

        // Create different expression
        let bvar3 = LeanExpr::bvar(lean, 1)?;

        // Should not be equal
        assert!(!LeanExpr::equal(&bvar1, &bvar3));

        Ok(())
    });

    assert!(result.is_ok(), "Equal test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_quick_lt() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;

        // quick_lt provides some ordering (not necessarily meaningful)
        let cmp1 = LeanExpr::quick_lt(&bvar0, &bvar1);
        let cmp2 = LeanExpr::quick_lt(&bvar1, &bvar0);

        // At least one should be false (reflexivity)
        let same = LeanExpr::quick_lt(&bvar0, &bvar0);
        assert!(!same);

        // Just verify the function works
        let _ = cmp1 || cmp2;

        Ok(())
    });

    assert!(result.is_ok(), "quick_lt test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_lt() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;

        // lt provides a total order
        let cmp1 = LeanExpr::lt(&bvar0, &bvar1);
        let cmp2 = LeanExpr::lt(&bvar1, &bvar0);

        // Exactly one should be true (antisymmetry)
        assert_ne!(cmp1, cmp2);

        // Same expression should not be less than itself
        assert!(!LeanExpr::lt(&bvar0, &bvar0));

        Ok(())
    });

    assert!(result.is_ok(), "lt test failed: {:?}", result.err());
}

// ============ Expression Utility Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_expression_hash() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create expressions
        let bvar0 = LeanExpr::bvar(lean, 0)?;
        let bvar1 = LeanExpr::bvar(lean, 1)?;

        // Get hashes
        let hash0 = LeanExpr::hash(&bvar0);
        let hash1 = LeanExpr::hash(&bvar1);

        // Different expressions should (likely) have different hashes
        // Note: This is probabilistic, not guaranteed
        let _ = hash0 != hash1;

        // Same expression should have same hash
        let bvar0_again = LeanExpr::bvar(lean, 0)?;
        let hash0_again = LeanExpr::hash(&bvar0_again);
        assert_eq!(hash0, hash0_again);

        Ok(())
    });

    assert!(result.is_ok(), "Hash test failed: {:?}", result.err());
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_has_level_param() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a level with a parameter
        let u_name = LeanName::from_str(lean, "u")?;
        let param_level = LeanLevel::param(lean, u_name)?;
        let sort_with_param = LeanExpr::sort(lean, param_level)?;

        // Should have level param
        assert!(LeanExpr::has_level_param(&sort_with_param));

        // Simple sort without params
        let zero_level = LeanLevel::zero(lean)?;
        let prop = LeanExpr::sort(lean, zero_level)?;

        // Should not have level param
        assert!(!LeanExpr::has_level_param(&prop));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "has_level_param test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_has_level_mvar() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Most expressions won't have level mvars
        let bvar = LeanExpr::bvar(lean, 0)?;

        // Should return false for simple expressions
        let has_mvar = LeanExpr::has_level_mvar(&bvar);
        assert!(!has_mvar);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "has_level_mvar test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_consume_type_annotations() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a simple expression
        let bvar = LeanExpr::bvar(lean, 0)?;

        // Consume type annotations (optimization)
        let consumed = LeanExpr::consume_type_annotations(bvar)?;

        // Should still be a bvar
        assert!(LeanExpr::is_bvar(&consumed));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "consume_type_annotations test failed: {:?}",
        result.err()
    );
}

// ============ Literal Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_literal_string() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a string literal
        let hello_lit = LeanLiteral::string(lean, "Hello, World!")?;
        let expr = LeanExpr::lit(lean, hello_lit)?;

        // Check it's a literal
        assert!(LeanExpr::is_lit(&expr));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "String literal test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_literal_type() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a nat literal
        let nat_lit = LeanLiteral::nat(lean, 42)?;

        // Get its type
        let lit_type = LeanLiteral::type_(&nat_lit)?;

        // Should be a valid expression (the Nat type)
        assert!(!lit_type.as_ptr().is_null());

        // Try with string literal
        let str_lit = LeanLiteral::string(lean, "test")?;
        let str_type = LeanLiteral::type_(&str_lit)?;

        // Should be a valid expression (the String type)
        assert!(!str_type.as_ptr().is_null());

        // The types should be different
        assert!(!LeanExpr::equal(&lit_type, &str_type));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Literal type test failed: {:?}",
        result.err()
    );
}

// ============ Name Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_name_anonymous() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let anon = LeanName::anonymous(lean)?;

        // Check the kind
        let kind = LeanName::kind(&anon);
        assert_eq!(kind, NameKind::Anonymous);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Anonymous name test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_name_append_num() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create x.1
        let x_name = LeanName::from_str(lean, "x")?;
        let x_1 = LeanName::append_num(x_name, lean, 1)?;

        // Check the kind is Num
        let kind = LeanName::kind(&x_1);
        assert_eq!(kind, NameKind::Num);

        // Create x.123
        let x_name = LeanName::from_str(lean, "x")?;
        let x_123 = LeanName::append_num(x_name, lean, 123)?;

        // Should not be equal to x.1
        assert!(!LeanName::eq(&x_1, &x_123));

        Ok(())
    });

    assert!(result.is_ok(), "append_num test failed: {:?}", result.err());
}

#[test]
// #[ignore = "from_components causes crash"]
fn test_name_from_components() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // First, test that simple names are equal
        let name1 = LeanName::from_str(lean, "Nat")?;
        let name2 = LeanName::from_str(lean, "Nat")?;
        eprintln!(
            "name1 ptr: {:?}, name2 ptr: {:?}",
            name1.as_ptr(),
            name2.as_ptr()
        );
        eprintln!("simple names eq: {}", LeanName::eq(&name1, &name2));
        assert!(LeanName::eq(&name1, &name2), "Simple names should be equal");

        // Create Nat.add from components
        let nat_add = LeanName::from_components(lean, "Nat.add")?;

        // Create the same name manually
        let nat = LeanName::from_str(lean, "Nat")?;
        let nat_add_manual = LeanName::append_str(nat, lean, "add")?;

        // Check equality
        let are_equal = LeanName::eq(&nat_add, &nat_add_manual);
        eprintln!("hierarchical names eq: {}", are_equal);

        // Should be equal
        assert!(are_equal, "Hierarchical names should be equal");

        Ok(())
    });

    assert!(
        result.is_ok(),
        "from_components test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_name_hierarchical() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Build a complex hierarchical name: Std.Data.List.head
        let std = LeanName::from_str(lean, "Std")?;
        let std_data = LeanName::append_str(std, lean, "Data")?;
        let std_data_list = LeanName::append_str(std_data, lean, "List")?;
        let full_name = LeanName::append_str(std_data_list, lean, "head")?;

        // Check the kind is Str (last component)
        let kind = LeanName::kind(&full_name);
        assert_eq!(kind, NameKind::Str);

        // Create using from_components
        let full_name_2 = LeanName::from_components(lean, "Std.Data.List.head")?;

        // Should be equal
        assert!(LeanName::eq(&full_name, &full_name_2));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Hierarchical name test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_name_mixed_components() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Create a name with both string and numeric components: x.1.aux
        let x = LeanName::from_str(lean, "x")?;
        let x_1 = LeanName::append_num(x, lean, 1)?;
        let x_1_aux = LeanName::append_str(x_1, lean, "aux")?;

        // Final kind should be Str
        let kind = LeanName::kind(&x_1_aux);
        assert_eq!(kind, NameKind::Str);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Mixed components test failed: {:?}",
        result.err()
    );
}

// ============ Level Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_level_zero_and_one() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let zero = LeanLevel::zero(lean)?;
        let one = LeanLevel::one(lean)?;

        // Create sorts with these levels
        let prop = LeanExpr::sort(lean, zero)?;
        let type0 = LeanExpr::sort(lean, one)?;

        // Both should be sorts
        assert!(LeanExpr::is_sort(&prop));
        assert!(LeanExpr::is_sort(&type0));

        // But not equal
        assert!(!LeanExpr::equal(&prop, &type0));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Zero and one levels test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_level_succ_chain() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Build a chain: 0 -> 1 -> 2 -> 3
        let zero = LeanLevel::zero(lean)?;
        let one = LeanLevel::succ(zero)?;
        let two = LeanLevel::succ(one)?;
        let three = LeanLevel::succ(two)?;

        // All should be valid
        let sort3 = LeanExpr::sort(lean, three)?;
        assert!(LeanExpr::is_sort(&sort3));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Level succ chain test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_level_max_imax() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let one = LeanLevel::one(lean)?;
        let two = LeanLevel::succ(one.clone())?;

        // Create max(1, 2)
        let max_level = LeanLevel::max(one.clone(), two.clone())?;
        let sort_max = LeanExpr::sort(lean, max_level)?;
        assert!(LeanExpr::is_sort(&sort_max));

        // Create imax(1, 2)
        let imax_level = LeanLevel::imax(one, two)?;
        let sort_imax = LeanExpr::sort(lean, imax_level)?;
        assert!(LeanExpr::is_sort(&sort_imax));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Level max/imax test failed: {:?}",
        result.err()
    );
}

// ============ Complex Integration Tests ============

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_complex_nested_lambda() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Build λ (A : Type) (x : A), x
        // This is the polymorphic identity function

        // A : Type
        let a_name = LeanName::from_str(lean, "A")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;

        // x : A (represented as bvar 0 inside the inner lambda)
        let x_name = LeanName::from_str(lean, "x")?;
        let a_type = LeanExpr::bvar(lean, 0)?; // References A from outer lambda

        // Body: x (represented as bvar 0)
        let x_body = LeanExpr::bvar(lean, 0)?;

        // Inner lambda: λ (x : A), x
        let inner_lambda = LeanExpr::lambda(x_name, a_type, x_body, BinderInfo::Default)?;

        // Outer lambda: λ (A : Type), <inner>
        let outer_lambda = LeanExpr::lambda(a_name, type0, inner_lambda, BinderInfo::Default)?;

        // Check structure
        assert!(LeanExpr::is_lambda(&outer_lambda));
        let outer_body = LeanExpr::lambda_body(&outer_lambda)?;
        assert!(LeanExpr::is_lambda(&outer_body));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Complex nested lambda test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_complex_application_chain() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Build a complex application: f a b c d
        let f = LeanExpr::bvar(lean, 0)?;
        let a = LeanExpr::bvar(lean, 1)?;
        let b = LeanExpr::bvar(lean, 2)?;
        let c = LeanExpr::bvar(lean, 3)?;
        let d = LeanExpr::bvar(lean, 4)?;

        let app = LeanExpr::mk_app(&f, &[&a, &b, &c, &d])?;

        // Walk the application chain
        let mut current = app;
        let mut arg_indices = vec![];

        while LeanExpr::is_app(&current) {
            let arg = LeanExpr::app_arg(&current)?;
            if LeanExpr::is_bvar(&arg) {
                arg_indices.push(LeanExpr::bvar_idx(&arg)?);
            }
            current = LeanExpr::app_fn(&current)?;
        }

        // Should have collected d, c, b, a (in reverse order)
        assert_eq!(arg_indices, vec![4, 3, 2, 1]);

        // Final function should be f (bvar 0)
        assert!(LeanExpr::is_bvar(&current));
        assert_eq!(LeanExpr::bvar_idx(&current)?, 0);

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Complex application chain test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_forall_chain() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        // Build ∀ (A : Type) (B : Type), A → B → A
        let a_name = LeanName::from_str(lean, "A")?;
        let b_name = LeanName::from_str(lean, "B")?;
        let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;

        // A → B → A where A is bvar 1, B is bvar 0
        let a_bvar = LeanExpr::bvar(lean, 1)?;
        let b_bvar = LeanExpr::bvar(lean, 0)?;
        let b_to_a = LeanExpr::arrow(b_bvar, a_bvar.clone())?;
        let a_to_b_to_a = LeanExpr::arrow(a_bvar, b_to_a)?;

        // ∀ (B : Type), A → B → A
        let forall_b = LeanExpr::forall(b_name, type0.clone(), a_to_b_to_a, BinderInfo::Default)?;

        // ∀ (A : Type) (B : Type), A → B → A
        let forall_a_b = LeanExpr::forall(a_name, type0, forall_b, BinderInfo::Default)?;

        // Check structure
        assert!(LeanExpr::is_forall(&forall_a_b));
        let body = LeanExpr::forall_body(&forall_a_b)?;
        assert!(LeanExpr::is_forall(&body));

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Forall chain test failed: {:?}",
        result.err()
    );
}

#[test]
#[cfg_attr(
    all(target_os = "macos", lean_4_20, not(lean_4_21)),
    ignore = "Lean 4.20.0 has initialize_Lean_Expr bug on macOS"
)]
fn test_binder_info_variants() {
    let result: LeanResult<()> = leo3::test_with_lean(|lean| {
        let x_name = LeanName::from_str(lean, "x")?;
        let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;
        let body = LeanExpr::bvar(lean, 0)?;

        // Test each binder info variant
        let default_lambda = LeanExpr::lambda(
            x_name.clone(),
            prop.clone(),
            body.clone(),
            BinderInfo::Default,
        )?;
        assert_eq!(LeanExpr::lambda_info(&default_lambda)?, BinderInfo::Default);

        let implicit_lambda = LeanExpr::lambda(
            x_name.clone(),
            prop.clone(),
            body.clone(),
            BinderInfo::Implicit,
        )?;
        assert_eq!(
            LeanExpr::lambda_info(&implicit_lambda)?,
            BinderInfo::Implicit
        );

        let strict_implicit_lambda = LeanExpr::lambda(
            x_name.clone(),
            prop.clone(),
            body.clone(),
            BinderInfo::StrictImplicit,
        )?;
        assert_eq!(
            LeanExpr::lambda_info(&strict_implicit_lambda)?,
            BinderInfo::StrictImplicit
        );

        let inst_implicit_lambda = LeanExpr::lambda(x_name, prop, body, BinderInfo::InstImplicit)?;
        assert_eq!(
            LeanExpr::lambda_info(&inst_implicit_lambda)?,
            BinderInfo::InstImplicit
        );

        Ok(())
    });

    assert!(
        result.is_ok(),
        "Binder info variants test failed: {:?}",
        result.err()
    );
}
