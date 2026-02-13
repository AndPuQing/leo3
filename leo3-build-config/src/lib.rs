#![cfg_attr(docsrs, feature(doc_cfg))]
//! Build-time configuration for Leo3 (Rust-Lean4 bindings).
//!
//! This crate provides functionality to detect Lean4 installations and
//! configure build settings appropriately. It should be called from
//! build scripts of crates that depend on leo3.

pub mod errors;
pub mod impl_;

use errors::cargo_warn;
use std::env;
use std::sync::OnceLock;

pub use impl_::{LeanConfig, LeanVersion};

static LEAN_CONFIG: OnceLock<LeanConfig> = OnceLock::new();

/// Main entry point: adds all Leo3 configuration to the current compilation.
///
/// ## Environment Variables
///
/// - `LEO3_NO_LEAN=1` - Skip Lean4 detection and linking (for compile-only tests)
/// - `LEAN_HOME` - Override Lean4 installation directory
/// - `LEAN_LIB_DIR` - Override Lean4 library directory
/// - `LEAN_INCLUDE_DIR` - Override Lean4 include directory
/// - `LEO3_CONFIG_FILE` - Path to a pre-built config file
/// - `LEO3_CROSS_LIB_DIR` - Cross-compile: Lean library directory
/// - `LEO3_CROSS_LEAN_VERSION` - Cross-compile: Lean version string
pub fn use_leo3_cfgs() {
    impl_::print_expected_cfgs();
    impl_::print_rerun_if_env_changed();

    if env::var("LEO3_NO_LEAN").is_ok() {
        cargo_warn!("LEO3_NO_LEAN set: skipping Lean4 detection and linking");
        cargo_warn!("Tests requiring Lean4 runtime will not run");
        return;
    }

    match get() {
        Ok(config) => {
            impl_::emit_link_config(&config);
            impl_::emit_version_cfgs(&config);
            println!("cargo:rerun-if-changed={}", config.lean_home.display());
        }
        Err(e) => {
            cargo_warn!("Failed to detect Lean4: {}", e);
            cargo_warn!("Leo3 will not function without Lean4 installed");
            cargo_warn!("Set LEO3_NO_LEAN=1 to build without Lean4 (compile-only)");
        }
    }
}

/// Resolve a `LeanConfig` with the following priority:
///
/// 1. `DEP_LEAN4_LEO3_CONFIG` env var (hex-encoded, set by `leo3-ffi` via `links = "lean4"`)
/// 2. `LEO3_CONFIG_FILE` env var (path to a key=value config file)
/// 3. Host detection (cross-compile → env → lake → elan → PATH)
fn get() -> Result<LeanConfig, String> {
    // Priority 1: Cargo DEP_* from upstream `links = "lean4"` crate
    if let Ok(hex) = env::var("DEP_LEAN4_LEO3_CONFIG") {
        return LeanConfig::from_cargo_dep_env(&hex).map_err(|e| e.to_string());
    }

    // Priority 2: user-supplied config file
    if let Ok(path) = env::var("LEO3_CONFIG_FILE") {
        let file = std::fs::File::open(&path)
            .map_err(|e| format!("failed to open LEO3_CONFIG_FILE '{}': {}", path, e))?;
        return LeanConfig::from_reader(std::io::BufReader::new(file)).map_err(|e| e.to_string());
    }

    // Priority 3: host detection
    impl_::detect_lean_config().map_err(|e| e.to_string())
}

/// Detect Lean4 configuration (cached).
///
/// Returns `Result<LeanConfig, String>` for backward compatibility.
pub fn get_lean_config() -> Result<LeanConfig, String> {
    if let Some(config) = LEAN_CONFIG.get() {
        return Ok(config.clone());
    }

    let config = get()?;
    let _ = LEAN_CONFIG.set(config.clone());
    Ok(config)
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_version_parsing() {
        // This test requires Lean to be installed
        // In CI, this might need to be conditional
    }
}
