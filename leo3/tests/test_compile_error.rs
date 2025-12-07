//! Compile-time error tests using trybuild
//!
//! These tests ensure that invalid code produces helpful error messages.
//! Inspired by PyO3's UI tests.

#[test]
fn ui_tests() {
    let t = trybuild::TestCases::new();

    // Run all UI tests in tests/ui/
    t.compile_fail("tests/ui/*.rs");
}
