//! Option operation tests for Leo3
//!
//! These tests demonstrate LeanOption functionality including creation,
//! checking, and value extraction.

use leo3::prelude::*;

#[test]
fn test_option_none() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let opt = LeanOption::none(lean)?;

        assert!(LeanOption::isNone(&opt));
        assert!(!LeanOption::isSome(&opt));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_some() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let value = LeanNat::from_usize(lean, 42)?;
        let opt = LeanOption::some(lean, value.cast())?;

        assert!(!LeanOption::isNone(&opt));
        assert!(LeanOption::isSome(&opt));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_get_some() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let value = LeanNat::from_usize(lean, 42)?;
        let opt = LeanOption::some(lean, value.cast())?;

        let retrieved = LeanOption::get(lean, &opt);
        assert!(retrieved.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_get_none() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let opt = LeanOption::none(lean)?;

        let retrieved = LeanOption::get(lean, &opt);
        assert!(retrieved.is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_to_rust_option_some() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let value = LeanNat::from_usize(lean, 100)?;
        let opt = LeanOption::some(lean, value.cast())?;

        let rust_opt = LeanOption::toRustOption(lean, &opt);
        assert!(rust_opt.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_to_rust_option_none() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let opt = LeanOption::none(lean)?;

        let rust_opt = LeanOption::toRustOption(lean, &opt);
        assert!(rust_opt.is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_with_string() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "hello")?;
        let opt = LeanOption::some(lean, s.cast())?;

        assert!(LeanOption::isSome(&opt));

        let retrieved = LeanOption::get(lean, &opt);
        assert!(retrieved.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_with_list() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create a list
        let list = LeanList::nil(lean)?;
        let elem = LeanNat::from_usize(lean, 1)?;
        let list = LeanList::cons(lean, elem.cast(), list)?;

        // Wrap it in Option.some
        let opt = LeanOption::some(lean, list.cast())?;

        assert!(LeanOption::isSome(&opt));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_pattern_matching() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test with Some
        let value = LeanNat::from_usize(lean, 42)?;
        let opt_some = LeanOption::some(lean, value.cast())?;

        match LeanOption::toRustOption(lean, &opt_some) {
            Some(_) => {
                // Expected path
            }
            None => {
                panic!("Expected Some, got None");
            }
        }

        // Test with None
        let opt_none = LeanOption::none(lean)?;

        match LeanOption::toRustOption(lean, &opt_none) {
            Some(_) => {
                panic!("Expected None, got Some");
            }
            None => {
                // Expected path
            }
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_option_nested() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create Option (Option Nat)
        let inner_value = LeanNat::from_usize(lean, 42)?;
        let inner_opt = LeanOption::some(lean, inner_value.cast())?;
        let outer_opt = LeanOption::some(lean, inner_opt.cast())?;

        assert!(LeanOption::isSome(&outer_opt));

        // Get inner option
        let inner = LeanOption::get(lean, &outer_opt);
        assert!(inner.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}
