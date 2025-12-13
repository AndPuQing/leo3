//! Tests for LeanThunk<'l, T>
//!
//! LeanThunk provides safe lazy evaluation wrappers.

use leo3::instance::LeanAny;
use leo3::prelude::*;
use leo3::thunk::{LeanThunk, LeanThunkType};

#[test]
fn test_thunk_type_size() {
    // LeanThunk should be pointer-sized (same as LeanBound)
    assert_eq!(
        std::mem::size_of::<LeanThunk<LeanAny>>(),
        std::mem::size_of::<*mut ()>()
    );
}

#[test]
fn test_thunk_marker_type() {
    // Verify the marker type exists and has the expected properties
    assert_eq!(
        std::mem::size_of::<LeanThunkType<LeanAny>>(),
        0,
        "Marker type should be zero-sized"
    );
}

#[test]
fn test_thunk_is_thunk_check() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A natural number is NOT a thunk
        let n = LeanNat::from_usize(lean, 42)?;
        let any: LeanBound<'_, LeanAny> = n.cast();
        assert!(!LeanThunk::<LeanAny>::is_thunk(&any));

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[test]
fn test_thunk_try_from_any_fails_for_non_thunk() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // A string is NOT a thunk
        let s = LeanString::mk(lean, "not a thunk")?;
        let any: LeanBound<'_, LeanAny> = s.cast();
        assert!(LeanThunk::<LeanAny>::try_from_any(any).is_none());

        Ok::<_, LeanError>(())
    })
    .unwrap();
}

#[cfg(test)]
mod api_tests {
    use super::*;
    use leo3::closure::LeanClosure;

    // These tests verify the API is correct even without runtime thunk objects

    #[test]
    fn test_thunk_api_available() {
        // Verify methods are available on the type
        fn _check_api<'l>(thunk: &LeanThunk<'l, LeanAny>) {
            let _pure: bool = thunk.is_pure();
        }
    }

    #[test]
    fn test_thunk_creation_signature() {
        // Verify new method has correct signature
        fn _check_new<'l>(closure: LeanClosure<'l>) -> LeanThunk<'l, LeanAny> {
            LeanThunk::new(closure)
        }
    }

    #[test]
    fn test_thunk_get_signature() {
        // Verify get methods have correct signatures
        fn _check_get<'a, 'l>(
            thunk: &'a LeanThunk<'l, LeanAny>,
        ) -> leo3::LeanBorrowed<'a, 'l, LeanAny> {
            thunk.get()
        }

        fn _check_get_owned<'l>(thunk: LeanThunk<'l, LeanAny>) -> LeanBound<'l, LeanAny> {
            thunk.get_owned()
        }
    }
}
