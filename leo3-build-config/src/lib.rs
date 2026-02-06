//! Build-time configuration for Leo3 (Rust-Lean4 bindings).
//!
//! This crate provides functionality to detect Lean4 installations and
//! configure build settings appropriately. It should be called from
//! build scripts of crates that depend on leo3.

use once_cell::sync::OnceCell;
use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Configuration for the Lean4 installation
#[derive(Debug, Clone)]
pub struct LeanConfig {
    /// Path to the Lean4 installation
    pub lean_home: PathBuf,
    /// Path to the Lean library directory
    pub lean_lib_dir: PathBuf,
    /// Path to the Lean include directory
    pub lean_include_dir: PathBuf,
    /// Lean version (e.g., "4.0.0")
    pub version: String,
}

static LEAN_CONFIG: OnceCell<LeanConfig> = OnceCell::new();

/// Main entry point: adds all Leo3 configuration to the current compilation.
/// ## Environment Variables
///
/// - `LEO3_NO_LEAN=1` - Skip Lean4 detection and linking (for compile-only tests)
/// - `LEAN_HOME` - Override Lean4 installation directory
/// - `LEAN_LIB_DIR` - Override Lean4 library directory
/// - `LEAN_INCLUDE_DIR` - Override Lean4 include directory
pub fn use_leo3_cfgs() {
    print_expected_cfgs();

    // Check if we should skip Lean entirely (for compile-only tests)
    if env::var("LEO3_NO_LEAN").is_ok() {
        eprintln!("cargo:warning=LEO3_NO_LEAN set: skipping Lean4 detection and linking");
        eprintln!("cargo:warning=Tests requiring Lean4 runtime will not run");
        return;
    }

    match get_lean_config() {
        Ok(config) => {
            // Emit configuration for linking
            emit_link_config(&config);

            // Emit Lean version cfg flags
            emit_version_cfgs(&config.version);

            // Emit rerun-if-changed for Lean installation
            println!("cargo:rerun-if-changed={}", config.lean_home.display());
        }
        Err(e) => {
            eprintln!("cargo:warning=Failed to detect Lean4: {}", e);
            eprintln!("cargo:warning=Leo3 will not function without Lean4 installed");
            eprintln!("cargo:warning=Set LEO3_NO_LEAN=1 to build without Lean4 (compile-only)");
        }
    }
}

/// Print expected cfg flags for cargo 1.77+
fn print_expected_cfgs() {
    println!("cargo:rustc-check-cfg=cfg(lean_4_0)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_1)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_2)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_3)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_4)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_5)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_6)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_7)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_8)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_9)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_10)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_11)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_12)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_13)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_14)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_15)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_16)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_17)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_18)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_19)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_20)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_21)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_22)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_23)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_24)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_25)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_26)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_27)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_28)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_29)");
    println!("cargo:rustc-check-cfg=cfg(lean_4_30)");
}

/// Detect Lean4 configuration
pub fn get_lean_config() -> Result<LeanConfig, String> {
    // Try to get from cache first
    if let Some(config) = LEAN_CONFIG.get() {
        return Ok(config.clone());
    }

    // Try multiple detection methods in order of preference
    let config = detect_from_env()
        .or_else(|_| detect_from_lake())
        .or_else(|_| detect_from_elan())
        .or_else(|_| detect_from_path())?;

    // Cache the result
    let _ = LEAN_CONFIG.set(config.clone());
    Ok(config)
}

/// Try to detect Lean from environment variables
fn detect_from_env() -> Result<LeanConfig, String> {
    let lean_home = env::var("LEAN_HOME")
        .or_else(|_| env::var("ELAN_HOME"))
        .map_err(|_| "LEAN_HOME or ELAN_HOME not set")?;

    let lean_home = PathBuf::from(lean_home);
    validate_lean_installation(&lean_home)
}

/// Try to detect Lean from `lake` command
fn detect_from_lake() -> Result<LeanConfig, String> {
    let output = Command::new("lake")
        .arg("--version")
        .output()
        .map_err(|e| format!("Failed to run lake: {}", e))?;

    if !output.status.success() {
        return Err("lake command failed".to_string());
    }

    // Get LEAN_HOME from lake env
    let output = Command::new("lake")
        .arg("env")
        .arg("printenv")
        .arg("LEAN_HOME")
        .output()
        .map_err(|e| format!("Failed to get LEAN_HOME from lake: {}", e))?;

    let lean_home = String::from_utf8_lossy(&output.stdout).trim().to_string();

    if lean_home.is_empty() {
        return Err("lake did not provide LEAN_HOME".to_string());
    }

    validate_lean_installation(&PathBuf::from(lean_home))
}

/// Try to detect Lean from `elan` toolchain manager
fn detect_from_elan() -> Result<LeanConfig, String> {
    let output = Command::new("elan")
        .arg("which")
        .arg("lean")
        .output()
        .map_err(|e| format!("Failed to run elan: {}", e))?;

    if !output.status.success() {
        return Err("elan command failed".to_string());
    }

    let lean_path = String::from_utf8_lossy(&output.stdout).trim().to_string();

    // Extract LEAN_HOME from the lean binary path
    // Typically: ~/.elan/toolchains/<version>/bin/lean
    let lean_bin = PathBuf::from(lean_path);
    let lean_home = lean_bin
        .parent() // bin
        .and_then(|p| p.parent()) // toolchain version
        .ok_or_else(|| "Could not determine LEAN_HOME from elan".to_string())?;

    validate_lean_installation(lean_home)
}

/// Try to detect Lean from PATH
fn detect_from_path() -> Result<LeanConfig, String> {
    let output = Command::new("which")
        .arg("lean")
        .output()
        .map_err(|e| format!("Failed to find lean in PATH: {}", e))?;

    if !output.status.success() {
        return Err("lean not found in PATH".to_string());
    }

    let lean_path = String::from_utf8_lossy(&output.stdout).trim().to_string();

    let lean_bin = PathBuf::from(lean_path);
    let lean_home = lean_bin
        .parent()
        .and_then(|p| p.parent())
        .ok_or_else(|| "Could not determine LEAN_HOME from PATH".to_string())?;

    validate_lean_installation(lean_home)
}

/// Validate a Lean installation and extract configuration
fn validate_lean_installation(lean_home: &Path) -> Result<LeanConfig, String> {
    if !lean_home.exists() {
        return Err(format!("Lean home does not exist: {}", lean_home.display()));
    }

    // Check for key directories and files
    let lean_include_dir = lean_home.join("include");
    let lean_lib_dir = lean_home.join("lib").join("lean");

    if !lean_include_dir.exists() {
        return Err(format!(
            "Include directory not found: {}",
            lean_include_dir.display()
        ));
    }

    // Get Lean version
    let lean_bin = lean_home.join("bin").join("lean");
    let version = get_lean_version(&lean_bin)?;

    Ok(LeanConfig {
        lean_home: lean_home.to_path_buf(),
        lean_lib_dir,
        lean_include_dir,
        version,
    })
}

/// Get Lean version from the binary
fn get_lean_version(lean_bin: &Path) -> Result<String, String> {
    let output = Command::new(lean_bin)
        .arg("--version")
        .output()
        .map_err(|e| format!("Failed to run lean --version: {}", e))?;

    if !output.status.success() {
        return Err("lean --version failed".to_string());
    }

    let version_output = String::from_utf8_lossy(&output.stdout);

    // Parse version from output like "Lean (version 4.0.0, ...)"
    let version = version_output
        .split_whitespace()
        .find_map(|word| {
            if word.starts_with('4') {
                Some(word.trim_end_matches(',').to_string())
            } else {
                None
            }
        })
        .ok_or_else(|| "Could not parse Lean version".to_string())?;

    Ok(version)
}

/// Emit link configuration for cargo
fn emit_link_config(config: &LeanConfig) {
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();

    // Add library search path
    // On Windows: need both lib/lean (for .lib import libraries) and bin (for DLLs at runtime)
    // On Unix: only need lib/lean
    println!(
        "cargo:rustc-link-search=native={}",
        config.lean_lib_dir.display()
    );

    // On Windows, also add bin directory to search path for DLLs
    if target_os == "windows" {
        let bin_dir = config.lean_home.join("bin");
        println!("cargo:rustc-link-search=native={}", bin_dir.display());
    }

    // Link against Lean shared libraries
    // Based on lean4/tests/lake/examples/reverse-ffi/Makefile
    // Order matters: dependencies first, then base libraries
    //
    // Different Lean versions have different library structures:
    // - Lean 4.0-4.19: leanshared only
    // - Lean 4.20+: Init_shared, leanshared_2, leanshared_1, leanshared
    //
    // On Windows, the Lean toolchains installed by elan commonly ship MinGW-style
    // `.dll.a` import libraries. For MSVC targets, we still use `link.exe`; these
    // archives are typically COFF and can be consumed by the MSVC linker when
    // passed verbatim.

    // Detect which libraries are available
    let has_init_shared = if target_os == "windows" {
        config.lean_lib_dir.join("libInit_shared.dll.a").exists()
    } else {
        config.lean_lib_dir.join("libInit_shared.so").exists()
            || config.lean_lib_dir.join("libInit_shared.dylib").exists()
    };

    let has_leanshared_2 = if target_os == "windows" {
        config.lean_lib_dir.join("libleanshared_2.dll.a").exists()
    } else {
        config.lean_lib_dir.join("libleanshared_2.so").exists()
            || config.lean_lib_dir.join("libleanshared_2.dylib").exists()
    };

    if target_os == "windows" {
        // Use verbatim to link against .dll.a files (MinGW import libraries)
        if has_init_shared {
            println!("cargo:rustc-link-lib=dylib:+verbatim=libInit_shared.dll.a");
        }
        if has_leanshared_2 {
            println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared_2.dll.a");
            println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared_1.dll.a");
        }
        println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared.dll.a");
    } else {
        // Unix: standard library names
        if has_init_shared {
            println!("cargo:rustc-link-lib=dylib=Init_shared");
        }
        if has_leanshared_2 {
            println!("cargo:rustc-link-lib=dylib=leanshared_2");
            println!("cargo:rustc-link-lib=dylib=leanshared_1");
        }
        println!("cargo:rustc-link-lib=dylib=leanshared");
    }

    // EXPERIMENTAL: Try linking without libLean.a on Windows to avoid symbol conflicts
    // The `l_Lean_*` symbols needed by leo3::meta might be available in the shared libraries
    //
    // TODO: If this works, we can enable it for all platforms. If it doesn't work,
    // we need to make the meta module optional or find another solution for Windows.
    if target_os != "windows" {
        let lib_lean_a = config.lean_lib_dir.join("libLean.a");
        if lib_lean_a.exists() {
            println!("cargo:rustc-link-lib=static=Lean");
        }
    }

    // On Windows, link additional system libraries required by Lean
    if target_os == "windows" {
        // Windows Socket library (required by Lean's networking functionality)
        println!("cargo:rustc-link-lib=dylib=Ws2_32");
        // Windows BCrypt library (required by Lean's cryptographic functionality)
        println!("cargo:rustc-link-lib=dylib=Bcrypt");
        // User Environment library
        println!("cargo:rustc-link-lib=dylib=Userenv");
    }

    // Add rpath so binaries can find the library at runtime
    // This is necessary for tests and executables on Unix-like systems
    // Note: Windows uses PATH environment variable instead of rpath
    if target_os != "windows" {
        // On Unix-like systems (Linux, macOS), use rpath
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            config.lean_lib_dir.display()
        );
    }

    // Add include path for bindgen (future use)
    println!("cargo:include={}", config.lean_include_dir.display());
}

/// Emit version-specific cfg flags
fn emit_version_cfgs(version: &str) {
    // Parse major.minor version
    let parts: Vec<&str> = version.split('.').collect();
    if parts.len() < 2 {
        return;
    }

    let major = parts[0].parse::<u32>().unwrap_or(0);
    let minor = parts[1].parse::<u32>().unwrap_or(0);

    if major != 4 {
        return;
    }

    // Emit cfg flags for this version and all earlier versions
    // e.g., Lean 4.3 gets lean_4_0, lean_4_1, lean_4_2, lean_4_3
    for v in 0..=minor {
        println!("cargo:rustc-cfg=lean_4_{}", v);
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_version_parsing() {
        // This test requires Lean to be installed
        // In CI, this might need to be conditional
    }
}
