//! Array operation tests for Leo3
//!
//! These tests demonstrate LeanArray functionality including creation,
//! element access, manipulation, and conversions.

use leo3::prelude::*;

#[test]
fn test_array_creation() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::empty(lean)?;

        assert!(LeanArray::isEmpty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_push() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::empty(lean)?;

        // Push a natural number
        let n = LeanNat::from_usize(lean, 42)?;
        let arr = LeanArray::push(arr, n.cast())?;

        assert_eq!(LeanArray::size(&arr), 1);
        assert!(!LeanArray::isEmpty(&arr));

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_push_multiple() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::empty(lean)?;

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
        let mut arr = LeanArray::empty(lean)?;

        // Push elements 10, 20, 30
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Get elements back
        let _elem0 = LeanArray::get(&arr, lean, 0).expect("Element 0 should exist");
        let _elem1 = LeanArray::get(&arr, lean, 1).expect("Element 1 should exist");
        let _elem2 = LeanArray::get(&arr, lean, 2).expect("Element 2 should exist");

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
        let mut arr = LeanArray::empty(lean)?;

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
        let arr = LeanArray::empty(lean)?;

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
        let mut arr = LeanArray::empty(lean)?;

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
        let arr = LeanArray::empty(lean)?;

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
        let mut arr = LeanArray::empty(lean)?;

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
        let mut arr = LeanArray::empty(lean)?;

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
        let mut arr = LeanArray::empty(lean)?;

        // Push string elements
        let s1 = LeanString::mk(lean, "Hello")?;
        let s2 = LeanString::mk(lean, "World")?;

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
        let mut arr = LeanArray::empty(lean)?;

        // Lean arrays can hold mixed types (all are lean_object*)
        let n = LeanNat::from_usize(lean, 42)?;
        let s = LeanString::mk(lean, "Hello")?;

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
        let mut inner = LeanArray::empty(lean)?;
        let n1 = LeanNat::from_usize(lean, 1)?;
        let n2 = LeanNat::from_usize(lean, 2)?;
        inner = LeanArray::push(inner, n1.cast())?;
        inner = LeanArray::push(inner, n2.cast())?;

        // Create outer array containing inner array
        let mut outer = LeanArray::empty(lean)?;
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
        let mut arr = LeanArray::empty(lean)?;

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

#[test]
fn test_array_empty_with_capacity() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create array with capacity for 100 elements
        let arr = LeanArray::emptyWithCapacity(lean, 100)?;

        assert!(LeanArray::isEmpty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);
        assert_eq!(LeanArray::capacity(&arr), 100);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_capacity() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let arr = LeanArray::empty(lean)?;

        // Empty array has 0 capacity
        assert_eq!(LeanArray::capacity(&arr), 0);

        // Push elements and check capacity increases
        let n = LeanNat::from_usize(lean, 42)?;
        let arr = LeanArray::push(arr, n.cast())?;

        // After first push, capacity should be > 0
        assert!(LeanArray::capacity(&arr) > 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_replicate() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create array with 10 copies of 42
        let val = LeanNat::from_usize(lean, 42)?;
        let arr = LeanArray::replicate(lean, 10, val.cast())?;

        assert_eq!(LeanArray::size(&arr), 10);

        // All elements should be accessible
        for i in 0..10 {
            assert!(LeanArray::get(&arr, lean, i).is_some());
        }

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_replicate_zero() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create array with 0 copies
        let val = LeanNat::from_usize(lean, 42)?;
        let arr = LeanArray::replicate(lean, 0, val.cast())?;

        assert!(LeanArray::isEmpty(&arr));
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_get_d() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::empty(lean)?;

        // Push elements [10, 20, 30]
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Get element within bounds - should return element
        let default = LeanNat::from_usize(lean, 999)?;
        let _elem = LeanArray::getD(&arr, lean, 1, default.cast())?;
        // elem should be 20, not 999

        // Get element out of bounds - should return default
        let default = LeanNat::from_usize(lean, 999)?;
        let _elem = LeanArray::getD(&arr, lean, 100, default.cast())?;
        // elem should be 999

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_back() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Empty array should return None
        let arr = LeanArray::empty(lean)?;
        assert!(LeanArray::back(&arr, lean).is_none());

        // Array with elements should return last element
        let mut arr = LeanArray::empty(lean)?;
        for i in 1..=5 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Should return the last element (50)
        let last = LeanArray::back(&arr, lean);
        assert!(last.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_array_back_after_pop() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let mut arr = LeanArray::empty(lean)?;

        // Push [10, 20, 30]
        for i in 1..=3 {
            let n = LeanNat::from_usize(lean, i * 10)?;
            arr = LeanArray::push(arr, n.cast())?;
        }

        // Back should be 30
        assert!(LeanArray::back(&arr, lean).is_some());

        // Pop and check back again
        arr = LeanArray::pop(arr)?;
        // Back should now be 20
        assert!(LeanArray::back(&arr, lean).is_some());

        Ok(())
    });

    assert!(result.is_ok());
}
