//! Array operation tests for Leo3
//!
//! These tests demonstrate LeanArray functionality including creation,
//! element access, manipulation, and conversions.

use leo3::prelude::*;

#[test]
fn test_array_creation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        assert!(LeanArray::is_empty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_push() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        // Push a natural number
        let n = LeanNat::from_usize(lean, 42)?;
        let arr = LeanArray::push(arr, n.cast())?;

        assert_eq!(LeanArray::size(&arr), 1);
        assert!(!LeanArray::is_empty(&arr));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_push_multiple() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Push multiple elements
        for i in 0..5 {
            let n = LeanNat::from_usize(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        assert_eq!(LeanArray::size(&arr), 5);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_get() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Push elements 10, 20, 30
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Get elements back
        let elem0 = LeanArray::get(&arr, lean, 0).expect("Element 0 should exist");
        let elem1 = LeanArray::get(&arr, lean, 1).expect("Element 1 should exist");
        let elem2 = LeanArray::get(&arr, lean, 2).expect("Element 2 should exist");

        // Note: Elements are returned as LeanAny, would need type-specific handling
        // For now, just check that we got something
        assert!(LeanArray::get(&arr, lean, 0).is_some());
        assert!(LeanArray::get(&arr, lean, 1).is_some());
        assert!(LeanArray::get(&arr, lean, 2).is_some());

        // Out of bounds should return None
        assert!(LeanArray::get(&arr, lean, 3).is_none());
        assert!(LeanArray::get(&arr, lean, 100).is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_set() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Create array with [10, 20, 30]
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Set element at index 1 to 100
        let new_elem = LeanNat::from_usize(lean, 100)?;
        arr = LeanArray::set(arr, 1, new_elem.cast())?;

        // Size should remain the same
        assert_eq!(LeanArray::size(&arr), 3);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_set_out_of_bounds() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        // Try to set element at index 0 in empty array - should return error
        let n = LeanNat::from_usize(lean, 42)?;
        let result = LeanArray::set(arr, 0, n.cast());

        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.to_string().contains("Index out of bounds"));
        }

        Ok::<(), LeanError>(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_pop() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Push three elements
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        assert_eq!(LeanArray::size(&arr), 3);

        // Pop one element
        arr = LeanArray::pop(arr)?;
        assert_eq!(LeanArray::size(&arr), 2);

        // Pop another
        arr = LeanArray::pop(arr)?;
        assert_eq!(LeanArray::size(&arr), 1);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_pop_empty() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        let arr = LeanArray::new(lean)?;

        // Try to pop from empty array - should return error
        let result = LeanArray::pop(arr);

        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.to_string().contains("Cannot pop from empty array"));
        }

        Ok::<(), LeanError>(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_swap() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Create array with [10, 20, 30]
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Swap elements at indices 0 and 2
        arr = LeanArray::swap(arr, 0, 2)?;

        // Array should now be [30, 20, 10]
        // Size should remain the same
        assert_eq!(LeanArray::size(&arr), 3);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_swap_out_of_bounds() {
    leo3::prepare_freethreaded_lean();

    let result = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Create array with one element
        let n = LeanNat::from_usize(lean, 42)?;
        arr = LeanArray::push(arr, n.cast())?;

        // Try to swap with out of bounds index - should return error
        let result = LeanArray::swap(arr, 0, 5);

        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.to_string().contains("Index out of bounds"));
        }

        Ok::<(), LeanError>(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_with_strings() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Push string elements
        let s1 = LeanString::new(lean, "Hello")?;
        let s2 = LeanString::new(lean, "World")?;

        arr = LeanArray::push(arr, s1.cast())?;
        arr = LeanArray::push(arr, s2.cast())?;

        assert_eq!(LeanArray::size(&arr), 2);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_mixed_types() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::new(lean)?;

        // Lean arrays can hold mixed types (all are lean_object*)
        let n = LeanNat::from_usize(lean, 42)?;
        let s = LeanString::new(lean, "Hello")?;

        arr = LeanArray::push(arr, n.cast())?;
        arr = LeanArray::push(arr, s.cast())?;

        assert_eq!(LeanArray::size(&arr), 2);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_nested() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create inner array
        let mut inner = LeanArray::new(lean)?;
        let n1 = LeanNat::from_usize(lean, 1)?;
        let n2 = LeanNat::from_usize(lean, 2)?;
        inner = LeanArray::push(inner, n1.cast())?;
        inner = LeanArray::push(inner, n2.cast())?;

        // Create outer array containing inner array
        let mut outer = LeanArray::new(lean)?;
        outer = LeanArray::push(outer, inner.cast())?;

        assert_eq!(LeanArray::size(&outer), 1);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_operations_sequence() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Test a sequence of operations
        let mut arr = LeanArray::new(lean)?;

        // Push [1, 2, 3, 4, 5]
        for i in 1..=5 {
            let n = LeanNat::from_usize(lean, i)?;
            arr = LeanArray::push(arr, n.cast())?;
        }
        assert_eq!(LeanArray::size(&arr), 5);

        // Pop one: [1, 2, 3, 4]
        arr = LeanArray::pop(arr)?;
        assert_eq!(LeanArray::size(&arr), 4);

        // Swap first and last: [4, 2, 3, 1]
        arr = LeanArray::swap(arr, 0, 3)?;
        assert_eq!(LeanArray::size(&arr), 4);

        // Set middle element: [4, 2, 100, 1]
        let new_val = LeanNat::from_usize(lean, 100)?;
        arr = LeanArray::set(arr, 2, new_val.cast())?;
        assert_eq!(LeanArray::size(&arr), 4);

        Ok(())
    });

    assert!(result.is_ok());
}
