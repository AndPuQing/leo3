//! Tests for EIO Exception error handling in MetaMContext::run()
//!
//! Unit tests for handle_eio_result and extract_message_data are in
//! leo3/src/meta/metam.rs (cfg(test) module).
//! This file tests the LeanError::Exception variant formatting.

use leo3::prelude::*;

#[test]
fn test_exception_display_formatting() {
    let err = LeanError::exception(false, "unknown free variable");
    let display = format!("{}", err);
    assert_eq!(display, "Lean exception: unknown free variable");

    let internal_err = LeanError::exception(true, "internal error occurred");
    let internal_display = format!("{}", internal_err);
    assert_eq!(
        internal_display,
        "Lean internal exception: internal error occurred"
    );
}

#[test]
fn test_exception_debug_formatting() {
    let err = LeanError::exception(false, "some error");
    let debug = format!("{:?}", err);
    assert!(debug.contains("Exception"));
    assert!(debug.contains("some error"));
    assert!(debug.contains("is_internal: false"));
}

#[test]
fn test_exception_is_error_trait() {
    let err = LeanError::exception(false, "test");
    // LeanError implements std::error::Error
    let _: &dyn std::error::Error = &err;
}

#[test]
fn test_exception_empty_message() {
    let err = LeanError::exception(false, "");
    let display = format!("{}", err);
    assert_eq!(display, "Lean exception: ");
}
