//! Build script for leo3-build-config.
//!
//! When the `resolve-config` feature is enabled (used by leo3-ffi's build-dep),
//! this script detects the Lean4 installation and writes the config to
//! `$OUT_DIR/leo3-build-config.txt` so that lib.rs can read it via `include_str!`.

#[cfg(feature = "resolve-config")]
#[path = "src/errors.rs"]
mod errors;
#[cfg(feature = "resolve-config")]
#[path = "src/impl_.rs"]
mod impl_;

fn main() {
    #[cfg(feature = "resolve-config")]
    resolve_config();

    #[cfg(not(feature = "resolve-config"))]
    {
        // Nothing to do — downstream crates read config via DEP_LEAN4_LEO3_CONFIG
    }
}

#[cfg(feature = "resolve-config")]
fn resolve_config() {
    use std::env;
    use std::path::PathBuf;

    impl_::print_rerun_if_env_changed();

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let config_path = out_dir.join("leo3-build-config.txt");

    // LEO3_NO_LEAN: write a sentinel empty file
    if env::var("LEO3_NO_LEAN").is_ok() {
        std::fs::write(&config_path, "").expect("failed to write sentinel config");
        return;
    }

    // LEO3_CONFIG_FILE: copy user-supplied config
    if let Ok(user_path) = env::var("LEO3_CONFIG_FILE") {
        let contents = std::fs::read_to_string(&user_path)
            .unwrap_or_else(|e| panic!("failed to read LEO3_CONFIG_FILE '{}': {}", user_path, e));
        std::fs::write(&config_path, contents).expect("failed to write config");
        return;
    }

    // Normal detection
    match impl_::detect_lean_config() {
        Ok(config) => {
            let mut file =
                std::fs::File::create(&config_path).expect("failed to create config file");
            config.to_writer(&mut file).expect("failed to write config");
        }
        Err(e) => {
            errors::cargo_warn!("Failed to detect Lean4: {}", e);
            // Write empty sentinel so downstream doesn't fail on missing file
            std::fs::write(&config_path, "").expect("failed to write sentinel config");
        }
    }
}
