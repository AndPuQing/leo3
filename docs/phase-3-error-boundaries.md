# Phase 3: Error Boundaries

## Status

Implemented for the current macro families.

## Goal

Unify proc-macro generated FFI behavior so recoverable failures are not handled
with ad hoc `expect(...)` calls or silent fallbacks.

## Decisions Made

### 1. Shared boundary helpers now live in `leo3::__private`

Added:

- `ffi_panic_boundary(...)` for object-returning extern wrappers
- `scalar_u64_ffi_panic_boundary(...)` for scalar-returning extern wrappers
- `abort_ffi_boundary(...)` as the explicit scalar failure path

These helpers centralize panic catching and error-to-boundary handling.

### 2. `#[leanclass]` now uses generated try wrappers plus one panic boundary

Generated `#[leanclass]` wrappers now:

- convert arguments using `Result`-based error propagation
- convert return values using `Result`-based error propagation
- avoid `.expect(...)` on recoverable conversion/allocation paths
- route the outer extern function through `ffi_panic_boundary(...)`

Hidden `pub(crate)` try wrappers are generated for testability.

### 3. `#[lean_instance]` no longer silently falls back for string conversions

Previously, `Repr` and `ToString` wrappers could return an empty string when
conversion failed. That fallback has been removed.

Now:

- object-returning typeclass wrappers use `ffi_panic_boundary(...)`
- `Hashable` uses `scalar_u64_ffi_panic_boundary(...)`

### 4. Scalar-returning extern wrappers have a stricter failure model

For signatures like `Hashable -> u64`, there is no sound way to return a Lean
panic object. The current explicit policy is:

- report the boundary failure
- abort the process

This is intentionally loud and explicit. It replaces silent fallback behavior.

## Validation Performed

- `cargo test --locked -p leo3-macros-backend`
- `cargo test --locked -p leo3 --features "macros,runtime-tests" --test test_leanclass --test test_lean_instance --test test_leanfn_macro --test test_macro_pipeline`
- `cargo test --locked -p leo3 --features macros --test test_compile_error`
- `cargo test --locked -p leo3 --doc --features macros`

## Remaining Work

1. decide whether more macro families should reuse the same helpers
2. define stronger runtime assertions for Lean panic object behavior itself
3. revisit whether scalar-returning externs can gain any richer diagnostics
