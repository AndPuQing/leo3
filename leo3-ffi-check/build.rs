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
        Ok(config) => config,
        Err(e) => {
            println!("cargo:warning=Failed to find Lean4: {}", e);
            println!("cargo:warning=Skipping FFI validation checks");
            return;
        }
    };

    println!("cargo:rerun-if-changed=../lean4/src/include/lean/lean.h");
    println!("cargo:rerun-if-env-changed=LEAN_INCLUDE_DIR");

    // Determine Lean include directory
    let lean_include_dir = env::var("LEAN_INCLUDE_DIR")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            // Try common locations
            let common_paths = [
                "/usr/local/include",
                "/usr/include",
                "/opt/homebrew/include",
                "../lean4/src/include",
            ];

            for path in &common_paths {
                let lean_h = PathBuf::from(path).join("lean/lean.h");
                if lean_h.exists() {
                    return Some(PathBuf::from(path));
                }
            }
            None
        });

    let lean_include_dir = match lean_include_dir {
        Some(dir) => dir,
        None => {
            println!("cargo:warning=Could not find lean/lean.h");
            println!("cargo:warning=Set LEAN_INCLUDE_DIR to specify location");
            return;
        }
    };

    let lean_h = lean_include_dir.join("lean/lean.h");
    if !lean_h.exists() {
        println!(
            "cargo:warning=lean.h not found at {}",
            lean_h.display()
        );
        return;
    }

    println!("cargo:info=Found lean.h at {}", lean_h.display());

    // Generate bindings using bindgen
    let bindings = bindgen::Builder::default()
        .header(lean_h.to_str().unwrap())
        .clang_arg(format!("-I{}", lean_include_dir.display()))
        // Allowlist items we want to check
        .allowlist_type("lean_object")
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
