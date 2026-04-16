//! Integration test covering the public macro golden path.

#![cfg(all(feature = "macros", feature = "runtime-tests"))]

use leo3::prelude::*;

#[derive(Clone, Debug, PartialEq)]
#[leanclass]
struct PipelineCounter {
    value: i32,
}

#[leanclass]
impl PipelineCounter {
    fn new(initial: i32) -> Self {
        Self { value: initial }
    }

    fn increment(&mut self, delta: i32) {
        self.value += delta;
    }

    fn get(&self) -> i32 {
        self.value
    }
}

#[leanmodule(name = "MacroPipeline")]
mod macro_pipeline {
    use leo3::prelude::*;

    #[leanfn(name = "macro_pipeline_add")]
    pub fn add(a: u64, b: u64) -> u64 {
        a + b
    }

    #[leanfn(name = "macro_pipeline_banner")]
    pub fn banner(name: String, count: i32) -> String {
        format!("{name} has {count} ticks")
    }
}

#[test]
fn test_macro_pipeline_rust_and_metadata_surface() {
    assert_eq!(macro_pipeline::add(20, 22), 42);
    assert_eq!(
        macro_pipeline::banner("counter".to_string(), 8),
        "counter has 8 ticks"
    );
    assert_eq!(
        PIPELINECOUNTER_LEAN_CLASS_DECL,
        "opaque PipelineCounter : Type"
    );
    assert!(PIPELINECOUNTER_LEAN_METHODS_DECL.contains("__lean_ffi_PipelineCounter_new"));
    assert!(PIPELINECOUNTER_LEAN_METHODS_DECL.contains("opaque PipelineCounter.increment"));
    assert_eq!(
        macro_pipeline::__leo3_metadata_add().name,
        "macro_pipeline_add"
    );
    assert_eq!(
        macro_pipeline::__leo3_metadata_banner().name,
        "macro_pipeline_banner"
    );
    let module_metadata = macro_pipeline::__leo3_module_metadata();
    let export_names: Vec<_> = module_metadata
        .exports
        .iter()
        .map(|item| item.name)
        .collect();
    assert_eq!(module_metadata.name, "MacroPipeline");
    assert_eq!(
        export_names,
        vec!["macro_pipeline_add", "macro_pipeline_banner"]
    );

    let _init_fn: unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void =
        initialize_MacroPipeline;
}

#[test]
fn test_macro_pipeline_ffi_round_trip() {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| -> LeanResult<()> {
        let sum = unsafe {
            let a = LeanUInt64::mk(lean, 20)?;
            let b = LeanUInt64::mk(lean, 22)?;
            let ptr = macro_pipeline::macro_pipeline_add(a.into_ptr(), b.into_ptr());
            let sum = LeanBound::<LeanUInt64>::from_owned_ptr(lean, ptr);
            LeanUInt64::to_u64(&sum)
        };
        assert_eq!(sum, 42);

        let message = unsafe {
            let name = LeanString::mk(lean, "counter")?;
            let count = LeanInt32::mk(lean, 8)?;
            let ptr = macro_pipeline::macro_pipeline_banner(name.into_ptr(), count.into_ptr());
            let message = LeanBound::<LeanString>::from_owned_ptr(lean, ptr);
            LeanString::cstr(&message)?.to_owned()
        };
        assert_eq!(message, "counter has 8 ticks");

        let value = unsafe {
            let initial = LeanInt32::mk(lean, 5)?;
            let counter_ptr = __lean_ffi_PipelineCounter_new(initial.into_ptr());
            let delta = LeanInt32::mk(lean, 3)?;
            let counter_ptr = __lean_ffi_PipelineCounter_increment(counter_ptr, delta.into_ptr());
            let value_ptr = __lean_ffi_PipelineCounter_get(counter_ptr);
            let value = LeanBound::<LeanInt32>::from_owned_ptr(lean, value_ptr);
            LeanInt32::to_i32(&value)
        };
        assert_eq!(value, 8);

        Ok(())
    })
    .unwrap();
}
