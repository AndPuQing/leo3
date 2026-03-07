//! Feature flag testing.
//!
//! These tests verify that the crate's minimal default surface remains usable
//! while optional subsystems become available behind named features.

use leo3::prelude::*;

#[test]
fn test_core_surface_always_available() {
    leo3::prepare_freethreaded_lean();

    let result: LeanResult<()> = leo3::with_lean(|lean| {
        let n = LeanNat::from_usize(lean, 42)?;
        assert_eq!(LeanNat::to_usize(&n)?, 42);

        let s = LeanString::mk(lean, "test")?;
        assert_eq!(LeanString::cstr(&s)?, "test");

        let arr = LeanArray::empty(lean)?;
        assert_eq!(LeanArray::size(&arr), 0);

        Ok(())
    });

    assert!(result.is_ok());
}

#[cfg(feature = "macros")]
mod macros_feature {
    use super::*;

    #[derive(Debug, PartialEq, IntoLean, FromLean)]
    struct FeaturePair(u64, u64);

    #[test]
    fn test_macros_feature_surface() {
        leo3::prepare_freethreaded_lean();

        let result: LeanResult<()> = leo3::with_lean(|lean| {
            let pair = FeaturePair(1, 2);
            let lean_pair = pair.into_lean(lean)?;
            let roundtrip = FeaturePair::from_lean(&lean_pair)?;
            assert_eq!(roundtrip, FeaturePair(1, 2));
            Ok(())
        });

        assert!(result.is_ok());
    }
}

#[cfg(feature = "meta")]
#[test]
fn test_meta_feature_surface() {
    fn _check<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, leo3::meta::LeanEnvironment>> {
        leo3::meta::LeanEnvironment::empty(lean, 0)
    }
}

#[cfg(feature = "io")]
#[test]
fn test_io_feature_surface() {
    fn _check<'l>(lean: Lean<'l>) -> LeanResult<Option<String>> {
        leo3::io::env::get_env(lean, "PATH")
    }
}

#[cfg(feature = "task")]
#[test]
fn test_task_feature_surface() {
    fn _check<'l>(value: LeanBound<'l, LeanNat>) -> leo3::task::LeanTask<'l, LeanNat> {
        leo3::task::LeanTask::pure(value)
    }
}

#[cfg(feature = "task")]
#[test]
fn test_promise_feature_surface() {
    fn _check<'l>(
        promise: &leo3::promise::LeanPromise<'l, leo3::instance::LeanAny>,
    ) -> leo3::task::LeanTask<'l, leo3::instance::LeanAny> {
        promise.task()
    }
}

#[cfg(feature = "module-loading")]
#[test]
fn test_module_loading_feature_surface() {
    fn _check(path: &str, name: &str) -> Result<leo3::module::LeanModule, String> {
        leo3::module::LeanModule::load(path, name)
    }
}

#[cfg(feature = "tokio")]
#[test]
fn test_tokio_feature_surface() {
    fn _check<F, R>(f: F) -> R
    where
        F: FnOnce() -> R,
    {
        leo3::tokio_bridge::lean_block_in_place(f)
    }
}
