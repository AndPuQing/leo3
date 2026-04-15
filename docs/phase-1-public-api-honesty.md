# Phase 1: Public API Honesty

## Status

In progress

## Goal

Ensure Leo3's stable default public surface does not expose APIs whose behavior
is knowingly placeholder or semantically misleading.

## Decisions Made

### 1. Placeholder container wrappers are not part of the stable default surface

The following APIs are now gated behind `experimental-containers`:

- `leo3::types::containers`
- `leo3::types::LeanHashMap`
- `leo3::types::LeanHashSet`
- `leo3::types::LeanRBMap`
- prelude re-exports for those types

Rationale:

- the current implementations are explicitly placeholder
- leaving them on the default surface makes the crate look more complete than it is
- gating preserves ongoing implementation work without misrepresenting the stable API

### 2. The experimental status must be visible everywhere a user looks

The `experimental-containers` decision is now reflected in:

- Cargo features
- crate docs
- README
- testing guide
- container module docs

### 3. The default surface contract is now compile-tested

A `trybuild` contract test asserts that `LeanHashMap` is unavailable without
the experimental feature.

Files:

- `leo3/tests/test_surface_contract.rs`
- `leo3/tests/surface_ui/default_no_containers.rs`

## Audit Summary

### Stable surface findings addressed in this phase

- placeholder container wrappers exposed from `types/mod.rs`
- placeholder container wrappers re-exported in `prelude`
- README capability table presenting placeholder containers as ordinary wrappers

### Remaining placeholder-like references after this phase

These still exist, but are not currently treated as stable-surface honesty
violations for Phase 1:

- experimental container implementation internals under `experimental-containers`
- internal comments such as runtime/context placeholders in non-user-facing code
- implementation comments in IO/meta code that do not change the public API contract

## Validation Performed

- `cargo test --locked -p leo3 --no-default-features --test test_features`
- `cargo test --locked -p leo3 --no-default-features --features experimental-containers --test test_features`
- `cargo test --locked -p leo3 --no-default-features --features "experimental-containers,macros,meta,io,module-loading,tokio" --test test_features`
- `cargo test --locked -p leo3 --features macros --test test_compile_error`
- `cargo test --locked -p leo3 --no-default-features --test test_surface_contract`
- `cargo test --locked -p leo3 --doc --no-default-features`
- `cargo test --locked -p leo3 --doc --features "macros,task,tokio"`

## Exit Criteria for Phase 1

Phase 1 can be considered complete when:

1. no known placeholder implementation remains on the stable default surface
2. docs do not advertise experimental behavior as stable
3. surface contract tests cover intentional gating decisions

## Next Candidates If More Honesty Cleanup Is Needed

- audit whether any non-container public APIs still have materially incomplete semantics
- decide whether additional APIs need:
  - explicit experimental gating
  - stronger docs warnings
  - removal until implemented
