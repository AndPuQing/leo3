//! Tests for the Lean code generation from #[leanclass] macro.
//!
//! Verifies that the generated `*_LEAN_CLASS_DECL` and `*_LEAN_METHODS_DECL`
//! string constants contain the expected Lean declarations.

use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
#[allow(dead_code)]
struct Widget {
    val: i32,
}

#[leanclass]
impl Widget {
    fn create(val: i32) -> Self {
        Widget { val }
    }

    fn value(&self) -> i32 {
        self.val
    }

    fn set_value(&mut self, val: i32) {
        self.val = val;
    }
}

#[test]
fn test_lean_class_decl_constant() {
    assert_eq!(WIDGET_LEAN_CLASS_DECL, "opaque Widget : Type");
}

#[test]
fn test_lean_methods_decl_contains_all_methods() {
    let decl = WIDGET_LEAN_METHODS_DECL;
    // Should have one line per method
    let lines: Vec<&str> = decl.lines().collect();
    assert_eq!(
        lines.len(),
        3,
        "Expected 3 method declarations, got: {decl}"
    );
}

#[test]
fn test_lean_methods_decl_static_method() {
    let decl = WIDGET_LEAN_METHODS_DECL;
    // Static method: no self param, returns Self → mapped to Widget
    assert!(
        decl.contains(
            r#"@[extern "__lean_ffi_Widget_create"] opaque Widget.create : Int32 → Widget"#
        ),
        "Missing or incorrect static method declaration in:\n{decl}"
    );
}

#[test]
fn test_lean_methods_decl_ref_method() {
    let decl = WIDGET_LEAN_METHODS_DECL;
    // &self method: Widget → return type
    assert!(
        decl.contains(
            r#"@[extern "__lean_ffi_Widget_value"] opaque Widget.value : Widget → Int32"#
        ),
        "Missing or incorrect &self method declaration in:\n{decl}"
    );
}

#[test]
fn test_lean_methods_decl_mut_ref_method() {
    let decl = WIDGET_LEAN_METHODS_DECL;
    // &mut self with () return: Widget → params → Widget (returns modified self)
    assert!(
        decl.contains(r#"@[extern "__lean_ffi_Widget_set_value"] opaque Widget.set_value : Widget → Int32 → Widget"#),
        "Missing or incorrect &mut self method declaration in:\n{decl}"
    );
}

#[test]
fn test_ffi_names_follow_pattern() {
    let decl = WIDGET_LEAN_METHODS_DECL;
    // All FFI names should follow __lean_ffi_{Struct}_{method}
    for line in decl.lines() {
        let ffi_start = line.find("\"__lean_ffi_").expect("FFI name not found");
        let ffi_end = line[ffi_start + 1..].find('"').unwrap() + ffi_start + 1;
        let ffi_name = &line[ffi_start + 1..ffi_end];
        assert!(
            ffi_name.starts_with("__lean_ffi_Widget_"),
            "FFI name {ffi_name} doesn't match expected pattern __lean_ffi_Widget_*"
        );
    }
}
