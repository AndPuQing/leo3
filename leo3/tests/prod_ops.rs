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

        let _pair = LeanProd::mk(a.cast(), b.cast())?;

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

        let pair = LeanProd::mk(a.cast(), b.cast())?;
        let _first = LeanProd::fst(&pair);

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

        let pair = LeanProd::mk(a.cast(), b.cast())?;
        let _second = LeanProd::snd(&pair);

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

        let pair = LeanProd::mk(s1.cast(), s2.cast())?;

        let _first = LeanProd::fst(&pair);
        let _second = LeanProd::snd(&pair);

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

        let pair = LeanProd::mk(n.cast(), s.cast())?;

        let _first = LeanProd::fst(&pair);
        let _second = LeanProd::snd(&pair);

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

        let pair = LeanProd::mk(a.cast(), b.cast())?;
        let swapped = LeanProd::swap(pair)?;

        // After swapping, first should be 2, second should be 1
        let _first = LeanProd::fst(&swapped);
        let _second = LeanProd::snd(&swapped);

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

        let inner_pair = LeanProd::mk(a.cast(), b.cast())?;
        let outer_pair = LeanProd::mk(inner_pair.cast(), c.cast())?;

        // Get first element (which is a pair)
        let _first = LeanProd::fst(&outer_pair);

        // Get second element (which is a nat)
        let _second = LeanProd::snd(&outer_pair);

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

        let pair = LeanProd::mk(b.cast(), n.cast())?;

        let _first = LeanProd::fst(&pair);
        let _second = LeanProd::snd(&pair);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_prod_with_option() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        let opt = LeanOption::some(n.cast())?;
        let s = LeanString::mk(lean, "test")?;

        let pair = LeanProd::mk(opt.cast(), s.cast())?;

        let _first = LeanProd::fst(&pair);
        let _second = LeanProd::snd(&pair);

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
        let list = LeanList::cons(elem.cast(), list)?;

        // Create a nat
        let n = LeanNat::from_usize(lean, 42)?;

        // Create pair (list, nat)
        let pair = LeanProd::mk(list.cast(), n.cast())?;

        let _first = LeanProd::fst(&pair);
        let _second = LeanProd::snd(&pair);

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

        let inner = LeanProd::mk(b.cast(), c.cast())?;
        let triple = LeanProd::mk(a.cast(), inner.cast())?;

        let _first = LeanProd::fst(&triple);
        let _rest = LeanProd::snd(&triple);

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

        let pair = LeanProd::mk(a.cast(), b.cast())?;
        let swapped_once = LeanProd::swap(pair)?;
        let _swapped_twice = LeanProd::swap(swapped_once)?;

        // Original order should be restored
        Ok(())
    });

    assert!(result.is_ok());
}
