fn main() {
    // Configure Lean4 FFI compilation
    leo3_build_config::use_leo3_cfgs();

    // Note: We no longer compile C wrappers for static inline functions.
    // All inline functions are now implemented directly in Rust in the
    // inline module (see src/inline.rs), following PyO3's approach.
}
