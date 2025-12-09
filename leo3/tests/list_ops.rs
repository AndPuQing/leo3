//! List operation tests for Leo3
//!
//! These tests demonstrate LeanList functionality including creation,
//! traversal, and list operations.

use leo3::prelude::*;

#[test]
fn test_list_nil() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let list = LeanList::nil(lean)?;

        assert!(LeanList::isEmpty(&list));
        assert_eq!(LeanList::length(&list), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_cons() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Create empty list
        let list = LeanList::nil(lean)?;

        // Add element 42
        let elem = LeanNat::from_usize(lean, 42)?;
        let list = LeanList::cons(lean, elem.cast(), list)?;

        assert!(!LeanList::isEmpty(&list));
        assert_eq!(LeanList::length(&list), 1);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_head() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Build list: [42]
        let list = LeanList::nil(lean)?;
        let elem = LeanNat::from_usize(lean, 42)?;
        let list = LeanList::cons(lean, elem.cast(), list)?;

        // Get head
        let head = LeanList::head(lean, &list);
        assert!(head.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_head_empty() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let list = LeanList::nil(lean)?;

        // Head of empty list should be None
        let head = LeanList::head(lean, &list);
        assert!(head.is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_tail() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Build list: [1, 2]
        let list = LeanList::nil(lean)?;
        let elem2 = LeanNat::from_usize(lean, 2)?;
        let list = LeanList::cons(lean, elem2.cast(), list)?;
        let elem1 = LeanNat::from_usize(lean, 1)?;
        let list = LeanList::cons(lean, elem1.cast(), list)?;

        // Get tail
        let tail = LeanList::tail(lean, &list);
        assert!(tail.is_some());

        let tail = tail.unwrap();
        assert_eq!(LeanList::length(&tail), 1);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_tail_empty() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let list = LeanList::nil(lean)?;

        // Tail of empty list should be None
        let tail = LeanList::tail(lean, &list);
        assert!(tail.is_none());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_length_multiple_elements() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Build list: [1, 2, 3, 4, 5]
        let mut list = LeanList::nil(lean)?;

        for i in (1..=5).rev() {
            let elem = LeanNat::from_usize(lean, i)?;
            list = LeanList::cons(lean, elem.cast(), list)?;
        }

        assert_eq!(LeanList::length(&list), 5);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_build_and_traverse() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Build list: [1, 2, 3]
        let list = LeanList::nil(lean)?;
        let elem3 = LeanNat::from_usize(lean, 3)?;
        let list = LeanList::cons(lean, elem3.cast(), list)?;
        let elem2 = LeanNat::from_usize(lean, 2)?;
        let list = LeanList::cons(lean, elem2.cast(), list)?;
        let elem1 = LeanNat::from_usize(lean, 1)?;
        let list = LeanList::cons(lean, elem1.cast(), list)?;

        assert_eq!(LeanList::length(&list), 3);

        // Traverse: get first element
        let head = LeanList::head(lean, &list);
        assert!(head.is_some());

        // Get rest of list
        let tail = LeanList::tail(lean, &list).unwrap();
        assert_eq!(LeanList::length(&tail), 2);

        // Get second element
        let head2 = LeanList::head(lean, &tail);
        assert!(head2.is_some());

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_list_with_strings() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        // Build list of strings: ["hello", "world"]
        let list = LeanList::nil(lean)?;
        let str2 = LeanString::mk(lean, "world")?;
        let list = LeanList::cons(lean, str2.cast(), list)?;
        let str1 = LeanString::mk(lean, "hello")?;
        let list = LeanList::cons(lean, str1.cast(), list)?;

        assert_eq!(LeanList::length(&list), 2);
        assert!(!LeanList::isEmpty(&list));

        Ok(())
    });

    assert!(result.is_ok());
}
