//! Tests for LeanBorrowed<'a, 'l, T>
//!
//! LeanBorrowed provides zero-copy borrowed references to Lean objects
//! without reference counting overhead.

use leo3::prelude::*;

#[test]
fn test_borrowed_from_bound() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create an owned LeanBound
        let n = LeanNat::from_usize(lean, 42)?;

        // Borrow it (zero-cost, no RC increment)
        let borrowed = n.as_borrowed();

        // Can access the pointer
        assert!(!borrowed.as_ptr().is_null());

        // Can upgrade to owned (increments RC)
        let owned = borrowed.to_owned();
        assert_eq!(LeanNat::to_usize(&owned)?, 42);

        // Original is still valid
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_borrowed_is_copy() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 100)?;
        let borrowed = n.as_borrowed();

        // LeanBorrowed is Copy - can be used multiple times
        let b1 = borrowed;
        let b2 = borrowed;
        let b3 = b1;

        // All point to the same object
        assert_eq!(b1.as_ptr(), b2.as_ptr());
        assert_eq!(b2.as_ptr(), b3.as_ptr());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_borrowed_string() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let s = LeanString::mk(lean, "Hello, Borrowed!")?;
        let borrowed = s.as_borrowed();

        // Upgrade to owned
        let owned = borrowed.to_owned();

        // Both should reference the same string content
        assert_eq!(LeanString::cstr(&owned)?, "Hello, Borrowed!");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_borrowed_lean_token() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        let borrowed = n.as_borrowed();

        // Can extract Lean token from borrowed
        let _token = borrowed.lean_token();

        // The token can be used to create new objects
        // (lifetime ensures this is safe)

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_borrowed_multiple_borrows() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;

        // Multiple concurrent borrows are fine
        let b1 = n.as_borrowed();
        let b2 = n.as_borrowed();
        let b3 = n.as_borrowed();

        // All valid simultaneously
        assert_eq!(b1.as_ptr(), b2.as_ptr());
        assert_eq!(b2.as_ptr(), b3.as_ptr());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_borrowed_size() {
    // LeanBorrowed should be pointer-sized (zero cost)
    assert_eq!(
        std::mem::size_of::<leo3::LeanBorrowed<leo3::instance::LeanAny>>(),
        std::mem::size_of::<*const ()>()
    );
}
