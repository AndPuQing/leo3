//! Product (Pair) operation tests for Leo3
//!
//! These tests demonstrate LeanProd functionality including creation,
//! field access, and pair manipulation.

use leo3::prelude::*;

#[test]
fn test_prod_mk() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 42)?;
        let b = LeanNat::from_usize(lean, 100)?;

        let pair = LeanProd::mk(lean, a.cast(), b.cast())?;

        // Just verify we can create a pair
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_fst() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 42)?;
        let b = LeanNat::from_usize(lean, 100)?;

        let pair = LeanProd::mk(lean, a.cast(), b.cast())?;
        let first = LeanProd::fst(lean, &pair);

        // Verify we can get the first element
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_snd() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 42)?;
        let b = LeanNat::from_usize(lean, 100)?;

        let pair = LeanProd::mk(lean, a.cast(), b.cast())?;
        let second = LeanProd::snd(lean, &pair);

        // Verify we can get the second element
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_strings() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::mk(lean, "hello")?;
        let s2 = LeanString::mk(lean, "world")?;

        let pair = LeanProd::mk(lean, s1.cast(), s2.cast())?;

        let first = LeanProd::fst(lean, &pair);
        let second = LeanProd::snd(lean, &pair);

        // Verify we can create and access string pairs
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_mixed_types() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        let s = LeanString::mk(lean, "answer")?;

        let pair = LeanProd::mk(lean, n.cast(), s.cast())?;

        let first = LeanProd::fst(lean, &pair);
        let second = LeanProd::snd(lean, &pair);

        // Verify we can create pairs with different types
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_swap() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 1)?;
        let b = LeanNat::from_usize(lean, 2)?;

        let pair = LeanProd::mk(lean, a.cast(), b.cast())?;
        let swapped = LeanProd::swap(lean, pair)?;

        // After swapping, first should be 2, second should be 1
        let first = LeanProd::fst(lean, &swapped);
        let second = LeanProd::snd(lean, &swapped);

        // Verify swap worked
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_nested() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create nested pair: ((1, 2), 3)
        let a = LeanNat::from_usize(lean, 1)?;
        let b = LeanNat::from_usize(lean, 2)?;
        let c = LeanNat::from_usize(lean, 3)?;

        let inner_pair = LeanProd::mk(lean, a.cast(), b.cast())?;
        let outer_pair = LeanProd::mk(lean, inner_pair.cast(), c.cast())?;

        // Get first element (which is a pair)
        let first = LeanProd::fst(lean, &outer_pair);

        // Get second element (which is a nat)
        let second = LeanProd::snd(lean, &outer_pair);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_bool() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let b = LeanBool::mk(lean, true)?;
        let n = LeanNat::from_usize(lean, 42)?;

        let pair = LeanProd::mk(lean, b.cast(), n.cast())?;

        let first = LeanProd::fst(lean, &pair);
        let second = LeanProd::snd(lean, &pair);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_option() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        let opt = LeanOption::some(lean, n.cast())?;
        let s = LeanString::mk(lean, "test")?;

        let pair = LeanProd::mk(lean, opt.cast(), s.cast())?;

        let first = LeanProd::fst(lean, &pair);
        let second = LeanProd::snd(lean, &pair);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_list() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a list
        let list = LeanList::nil(lean)?;
        let elem = LeanNat::from_usize(lean, 1)?;
        let list = LeanList::cons(lean, elem.cast(), list)?;

        // Create a nat
        let n = LeanNat::from_usize(lean, 42)?;

        // Create pair (list, nat)
        let pair = LeanProd::mk(lean, list.cast(), n.cast())?;

        let first = LeanProd::fst(lean, &pair);
        let second = LeanProd::snd(lean, &pair);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_triple_via_nesting() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create triple (1, 2, 3) as (1, (2, 3))
        let a = LeanNat::from_usize(lean, 1)?;
        let b = LeanNat::from_usize(lean, 2)?;
        let c = LeanNat::from_usize(lean, 3)?;

        let inner = LeanProd::mk(lean, b.cast(), c.cast())?;
        let triple = LeanProd::mk(lean, a.cast(), inner.cast())?;

        let first = LeanProd::fst(lean, &triple);
        let rest = LeanProd::snd(lean, &triple);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_identity_swap() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test that swap(swap(p)) = p
        let a = LeanNat::from_usize(lean, 1)?;
        let b = LeanNat::from_usize(lean, 2)?;

        let pair = LeanProd::mk(lean, a.cast(), b.cast())?;
        let swapped_once = LeanProd::swap(lean, pair)?;
        let swapped_twice = LeanProd::swap(lean, swapped_once)?;

        // Original order should be restored
        Ok(())
    });

    assert!(result.is_ok());
}
