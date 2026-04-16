//! Compile-time surface contract tests.
//!
//! These tests protect the intended default public API from accidental
//! re-exports.

#![cfg(not(feature = "experimental-containers"))]

#[test]
fn default_surface_ui_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/surface_ui/*.rs");
}
