fn main() {
    // Configure Lean4 FFI compilation
    leo3_build_config::use_leo3_cfgs();

    // Emit hex-encoded config for downstream crates via Cargo's DEP_* mechanism.
    // Because leo3-ffi declares `links = "lean4"`, Cargo sets
    // `DEP_LEAN4_LEO3_CONFIG` for any crate that depends on leo3-ffi.
    if let Ok(config) = leo3_build_config::get_lean_config() {
        println!("cargo:LEO3_CONFIG={}", config.to_cargo_dep_env());
    }

    // Note: We no longer compile C wrappers for static inline functions.
    // All inline functions are now implemented directly in Rust in the
    // inline module (see src/inline.rs), following PyO3's approach.
}
