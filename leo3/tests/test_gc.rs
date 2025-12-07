//! Garbage collection and reference counting tests
//!
//! These tests verify that Leo3's reference counting works correctly
//! and that objects are properly cleaned up.
//!
//! Inspired by PyO3's test_gc.rs

use leo3::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// Helper to track drop calls
struct DropCounter {
    counter: Arc<AtomicUsize>,
}

impl DropCounter {
    fn new(counter: Arc<AtomicUsize>) -> Self {
        counter.fetch_add(1, Ordering::SeqCst);
        Self { counter }
    }
}

impl Drop for DropCounter {
    fn drop(&mut self) {
        self.counter.fetch_sub(1, Ordering::SeqCst);
    }
}

#[test]
fn test_basic_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create an object
        let n = LeanNat::from_usize(lean, 42)?;

        // Clone should increment refcount
        let n2 = n.clone();

        // Both should be valid
        assert_eq!(LeanNat::to_usize(&n)?, 42);
        assert_eq!(LeanNat::to_usize(&n2)?, 42);

        // When both drop, refcount should reach 0
        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_clone_and_drop() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n1 = LeanNat::from_usize(lean, 100)?;

        // Create multiple clones
        let n2 = n1.clone();
        let n3 = n1.clone();
        let n4 = n2.clone();

        // All should have same value
        assert_eq!(LeanNat::to_usize(&n1)?, 100);
        assert_eq!(LeanNat::to_usize(&n2)?, 100);
        assert_eq!(LeanNat::to_usize(&n3)?, 100);
        assert_eq!(LeanNat::to_usize(&n4)?, 100);

        // Drop them one by one (implicit at end of scope)
        drop(n4);
        drop(n3);
        drop(n2);
        // n1 drops at end of scope

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_unbind_rebind_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create bound object
        let n = LeanNat::from_usize(lean, 42)?;

        // Unbind to LeanRef
        let n_ref = n.unbind();

        // Rebind should work
        let n2 = n_ref.bind(lean);
        assert_eq!(LeanNat::to_usize(&n2)?, 42);

        // Clone the ref
        let n_ref2 = n_ref.clone();

        // Both refs should be valid
        let n3 = n_ref.bind(lean);
        let n4 = n_ref2.bind(lean);
        assert_eq!(LeanNat::to_usize(&n3)?, 42);
        assert_eq!(LeanNat::to_usize(&n4)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::new(lean, "Hello, World!")?;

        // Clone string
        let s2 = s1.clone();

        // Both should be equal
        assert!(LeanString::eq(&s1, &s2));
        assert_eq!(LeanString::to_str(&s1)?, LeanString::to_str(&s2)?);

        // Drop one
        drop(s2);

        // s1 should still be valid
        assert_eq!(LeanString::to_str(&s1)?, "Hello, World!");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Add elements
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Clone array
        let arr2 = arr.clone();

        // Both should have same size
        assert_eq!(LeanArray::size(&arr), 3);
        assert_eq!(LeanArray::size(&arr2), 3);

        // Drop one
        drop(arr2);

        // Original should still be valid
        assert_eq!(LeanArray::size(&arr), 3);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_nested_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create nested structure: array of strings
        let mut arr = LeanArray::new(lean)?;

        let s1 = LeanString::new(lean, "First")?;
        let s2 = LeanString::new(lean, "Second")?;
        let s3 = LeanString::new(lean, "Third")?;

        // Keep clones of strings
        let s1_clone = s1.clone();
        let s2_clone = s2.clone();

        // Add to array (array gets its own references)
        arr = LeanArray::push(arr, s1.cast())?;
        arr = LeanArray::push(arr, s2.cast())?;
        arr = LeanArray::push(arr, s3.cast())?;

        // Clones should still be valid
        assert_eq!(LeanString::to_str(&s1_clone)?, "First");
        assert_eq!(LeanString::to_str(&s2_clone)?, "Second");

        // Drop array (should not invalidate our clones)
        drop(arr);

        // Clones should still work
        assert_eq!(LeanString::to_str(&s1_clone)?, "First");
        assert_eq!(LeanString::to_str(&s2_clone)?, "Second");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_cast_preserves_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;

        // Clone before cast
        let n_clone = n.clone();

        // Cast to LeanAny
        let any = n.cast();

        // Original clone should still be valid
        assert_eq!(LeanNat::to_usize(&n_clone)?, 42);

        // Drop the any
        drop(any);

        // Clone should still work
        assert_eq!(LeanNat::to_usize(&n_clone)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_multiple_scopes() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n_ref = {
            // Create in inner scope
            let n = LeanNat::from_usize(lean, 100)?;
            n.unbind()
        }; // n drops here, but n_ref keeps object alive

        // Object should still be accessible via n_ref
        let n2 = n_ref.bind(lean);
        assert_eq!(LeanNat::to_usize(&n2)?, 100);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_operations_preserve_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let a = LeanNat::from_usize(lean, 10)?;
        let b = LeanNat::from_usize(lean, 32)?;

        // Keep clones before operation
        let a_clone = a.clone();
        let b_clone = b.clone();

        // Perform operation (consumes a and b)
        let sum = LeanNat::add(a, b)?;

        // Clones should still be valid
        assert_eq!(LeanNat::to_usize(&a_clone)?, 10);
        assert_eq!(LeanNat::to_usize(&b_clone)?, 32);
        assert_eq!(LeanNat::to_usize(&sum)?, 42);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_string_operations_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let s1 = LeanString::new(lean, "Hello, ")?;
        let s2 = LeanString::new(lean, "World!")?;

        // Keep clones
        let s1_clone = s1.clone();
        let s2_clone = s2.clone();

        // Append (consumes s1, borrows s2)
        let s3 = LeanString::append(s1, &s2)?;

        // s1_clone and s2_clone and s2 should still be valid
        assert_eq!(LeanString::to_str(&s1_clone)?, "Hello, ");
        assert_eq!(LeanString::to_str(&s2_clone)?, "World!");
        assert_eq!(LeanString::to_str(&s2)?, "World!");
        assert_eq!(LeanString::to_str(&s3)?, "Hello, World!");

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_operations_refcount() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Clone empty array
        let arr_clone1 = arr.clone();

        // Push element
        let n = LeanNat::from_usize(lean, 42)?;
        arr = LeanArray::push(arr, n.cast())?;

        // Clone after push
        let arr_clone2 = arr.clone();

        // All arrays should be valid
        assert_eq!(LeanArray::size(&arr_clone1), 0); // Original empty
        assert_eq!(LeanArray::size(&arr), 1);
        assert_eq!(LeanArray::size(&arr_clone2), 1);

        // Pop from arr
        arr = LeanArray::pop(arr)?;

        // Clones should not be affected
        assert_eq!(LeanArray::size(&arr), 0);
        assert_eq!(LeanArray::size(&arr_clone2), 1); // Still has element

        Ok(())
    });

    assert!(result.is_ok());
}
