# Phase 4: Module Surface

## Status

First implementation pass completed.

## What Changed

### Structured `#[leanmodule]` parsing

`#[leanmodule]` no longer parses attributes by string manipulation.

It now supports structured forms:

- `#[leanmodule]`
- `#[leanmodule(MyModule)]`
- `#[leanmodule(name = "MyModule")]`
- `#[leanmodule(crate = my::leo3)]`
- `#[leanmodule(name = "MyModule", crate = my::leo3)]`

### Crate-path-aware generated code

Generated module init code can now target a re-exported `leo3` path, matching
the configurability already present in other macros.

### Metadata-driven implicit export registration

`#[leanmodule]` now treats inline `#[leanfn]` items inside the module as the
module's implicit export set.

The macro generates `__leo3_module_metadata()` alongside the init symbol so
downstream Rust code can inspect the Lean-visible export names chosen for that
module. This does not yet replace real shared-library registration metadata, but
it makes the intended authoring model explicit: init is one concern, and export
discovery is another.

## Validation

- unit tests in `leo3-macros` cover option parsing
- runtime/module integration tests still pass
- `leo3/tests/test_leanmodule.rs` validates module metadata for inline
  `#[leanfn]` exports
- `leo3/tests/test_leanmodule_loading.rs` builds a real downstream `cdylib`
  fixture as a golden-path artifact check
- compile-fail suite still passes

## Follow-Up

This is still not the full shared-library registration story from the spec yet,
but it moves `#[leanmodule]` past "just make an init symbol" and gives Leo3 an
explicit module authoring model.
