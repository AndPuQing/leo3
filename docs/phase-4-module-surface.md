# Phase 4: Module Surface

## Status

First implementation pass completed

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

## Validation

- unit tests in `leo3-macros` cover option parsing
- runtime/module integration tests still pass
- compile-fail suite still passes

## Follow-Up

This is not the full module-system completion work from the spec yet. It fixes
the most brittle parsing layer and aligns the user-facing attribute surface with
the rest of the macro system.
