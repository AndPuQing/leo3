//! Example: end-to-end macro pipeline with `#[leanmodule]`, `#[leanfn]`, and `#[leanclass]`.

#![allow(unused_imports)]

use leo3::prelude::*;

#[derive(Clone, Debug, PartialEq)]
#[leanclass]
struct Counter {
    value: i32,
}

#[leanclass]
impl Counter {
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

#[leanmodule(name = "CounterDemo")]
mod counter_demo {
    use leo3::prelude::*;

    #[allow(unused_imports)]
    #[leanfn(name = "counter_demo_add")]
    pub fn add(a: u64, b: u64) -> u64 {
        a + b
    }

    #[allow(unused_imports)]
    #[leanfn(name = "counter_demo_banner")]
    pub fn banner(name: String, count: i32) -> String {
        format!("{name} has {count} ticks")
    }
}

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        println!("=== Macro Pipeline Example ===");
        println!("Lean class declaration:\n{}\n", COUNTER_LEAN_CLASS_DECL);
        println!("Lean method declarations:\n{}\n", COUNTER_LEAN_METHODS_DECL);

        let init_fn: unsafe extern "C" fn(u8, *mut std::ffi::c_void) -> *mut std::ffi::c_void =
            initialize_CounterDemo;
        println!(
            "Module init symbol is available at {:p}",
            init_fn as *const ()
        );

        let rust_sum = counter_demo::add(20, 22);
        println!("Rust call: add(20, 22) = {}", rust_sum);

        let sum = unsafe {
            let a = LeanUInt64::mk(lean, 20)?;
            let b = LeanUInt64::mk(lean, 22)?;
            let ptr = counter_demo::counter_demo_add(a.into_ptr(), b.into_ptr());
            let sum = LeanBound::<LeanUInt64>::from_owned_ptr(lean, ptr);
            LeanUInt64::to_u64(&sum)
        };
        println!("FFI call: add(20, 22) = {}", sum);

        let counter_value = unsafe {
            let initial = LeanInt32::mk(lean, 5)?;
            let counter_ptr = __lean_ffi_Counter_new(initial.into_ptr());
            let delta = LeanInt32::mk(lean, 3)?;
            let counter_ptr = __lean_ffi_Counter_increment(counter_ptr, delta.into_ptr());
            let value_ptr = __lean_ffi_Counter_get(counter_ptr);
            let value = LeanBound::<LeanInt32>::from_owned_ptr(lean, value_ptr);
            LeanInt32::to_i32(&value)
        };

        let banner = counter_demo::banner("counter".to_string(), counter_value);
        println!("{}", banner);

        let ffi_banner = unsafe {
            let name = LeanString::mk(lean, "counter")?;
            let count = LeanInt32::mk(lean, counter_value)?;
            let ptr = counter_demo::counter_demo_banner(name.into_ptr(), count.into_ptr());
            let message = LeanBound::<LeanString>::from_owned_ptr(lean, ptr);
            LeanString::cstr(&message)?.to_owned()
        };
        println!("FFI banner: {}", ffi_banner);

        Ok(())
    })
}
