fn main() {
    leo3_build_config::impl_::print_expected_cfgs();
    leo3_build_config::impl_::print_rerun_if_env_changed();

    // Get Lean config exclusively from leo3-ffi's DEP_LEAN4_LEO3_CONFIG.
    // This ensures leo3 and leo3-ffi always agree on version cfg flags,
    // avoiding mismatches during `cargo publish` verification where
    // leo3-ffi is rebuilt from the registry.
    if let Ok(hex) = std::env::var("DEP_LEAN4_LEO3_CONFIG") {
        match leo3_build_config::LeanConfig::from_cargo_dep_env(&hex) {
            Ok(config) => {
                leo3_build_config::impl_::emit_link_config(&config);
                leo3_build_config::impl_::emit_version_cfgs(&config);
            }
            Err(e) => {
                println!(
                    "cargo:warning=Failed to decode DEP_LEAN4_LEO3_CONFIG: {}",
                    e
                );
            }
        }
    } else if std::env::var("LEO3_NO_LEAN").is_ok() {
        println!("cargo:warning=LEO3_NO_LEAN set: skipping Lean4 configuration");
    } else {
        println!(
            "cargo:warning=DEP_LEAN4_LEO3_CONFIG not set; leo3-ffi may not have detected Lean"
        );
    }
}
