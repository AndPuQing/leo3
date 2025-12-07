//! Build script for Lean integration tests
//!
//! This compiles Lean code in the lean/ directory and links it with Rust tests.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=lean/");

    // Check if Lake is available
    let lake_available = Command::new("lake")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false);

    if !lake_available {
        println!("cargo:warning=Lake not found, skipping Lean compilation");
        println!("cargo:warning=Lean integration tests will not run");
        return;
    }

    // Get the Lean source directory
    let lean_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("lean");

    // Try to build Lean code with Lake
    let build_result = Command::new("lake")
        .arg("build")
        .current_dir(&lean_dir)
        .status();

    match build_result {
        Ok(status) if status.success() => {
            println!("cargo:info=Successfully built Lean code");

            // Tell cargo where to find the compiled Lean libraries
            let build_dir = lean_dir.join(".lake/build/lib");
            if build_dir.exists() {
                println!("cargo:rustc-link-search=native={}", build_dir.display());
            }

            // Link against the compiled Lean package
            // Note: The actual library name depends on the Lake configuration
            // println!("cargo:rustc-link-lib=static=Leo3Tests");
        }
        Ok(status) => {
            println!("cargo:warning=Lake build failed with status: {}", status);
            println!("cargo:warning=Lean integration tests will not run");
        }
        Err(e) => {
            println!("cargo:warning=Failed to run lake: {}", e);
            println!("cargo:warning=Lean integration tests will not run");
        }
    }

    // Use leo3-build-config to set up Lean linkage
    leo3_build_config::use_leo3_cfgs();
}
