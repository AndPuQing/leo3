//! Build script for leo3-ffi-check
//!
//! This generates Rust bindings from Lean4's actual C headers using bindgen,
//! then compares them against our hand-written FFI bindings to ensure correctness.
//!
//! Inspired by PyO3's pyo3-ffi-check crate.

use std::env;
use std::path::PathBuf;

fn main() {
    // Get Lean4 configuration
    let lean_config = match leo3_build_config::get_lean_config() {
        Ok(config) => {
            println!("cargo:info=Found Lean4 at {}", config.lean_home.display());
            config
        }
        Err(e) => {
            println!("cargo:warning=Failed to find Lean4: {}", e);
            println!("cargo:warning=Skipping FFI validation checks");
            return;
        }
    };

    println!("cargo:rerun-if-changed=../lean4/src/include/lean/lean.h");
    println!("cargo:rerun-if-env-changed=LEAN_INCLUDE_DIR");

    // Use the include directory from Lean config
    // LEAN_INCLUDE_DIR env var can override if needed
    let lean_include_dir = env::var("LEAN_INCLUDE_DIR")
        .ok()
        .map(PathBuf::from)
        .unwrap_or_else(|| lean_config.lean_include_dir.clone());

    let lean_h = lean_include_dir.join("lean/lean.h");
    if !lean_h.exists() {
        println!("cargo:warning=lean.h not found at {}", lean_h.display());
        return;
    }

    println!("cargo:info=Found lean.h at {}", lean_h.display());

    // Generate bindings using bindgen
    let bindings = bindgen::Builder::default()
        .header(lean_h.to_str().unwrap())
        .clang_arg(format!("-I{}", lean_include_dir.display()))
        // Allowlist items we want to check
        .allowlist_type("lean_object")
        .allowlist_type("lean_array_object")
        .allowlist_type("lean_sarray_object")
        .allowlist_type("lean_string_object")
        .allowlist_type("lean_closure_object")
        .allowlist_type("lean_ctor_object")
        .allowlist_type("lean_ref_object")
        .allowlist_type("lean_external_object")
        .allowlist_function("lean_.*")
        // Derive Debug for easier comparison
        .derive_debug(true)
        .derive_default(false)
        // Generate layout tests
        .layout_tests(true)
        // Don't generate comments
        .generate_comments(false)
        // Parse callbacks for better type handling
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Failed to generate bindings");

    // Write bindings to OUT_DIR
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindgen.rs");
    bindings
        .write_to_file(&out_path)
        .expect("Failed to write bindings");

    println!("cargo:info=Generated bindings at {}", out_path.display());
}
