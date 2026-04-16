# Leo3 Remaining Work Checklist

This file is the post-update snapshot after the current hardening pass.

The old four-item list no longer reflects the codebase accurately:

- `#[leanmodule]` now has an explicit metadata-driven export model for inline
  `#[leanfn]` items.
- external objects now have a documented borrow-first path via
  `borrow()`, `try_get_mut()`, and `try_take_inner()`.
- architecture and contributor docs now exist.

The main unresolved item is still containers.

## Current Top Priority

### P1: Experimental containers still need real Lean semantics

Status:
- Not complete.
- Still explicitly experimental.

Why it remains open:
- The wrappers are still placeholder implementations.
- The missing piece is not API shape anymore; it is the actual runtime instance
  and FFI story for `BEq`, `Hashable`, and `Ord`.

Code evidence:
- `leo3/src/types/containers/hashmap.rs`
- `leo3/src/types/containers/hashset.rs`
- `leo3/src/types/containers/rbmap.rs`
- `leo3/src/types/containers/README.md`

What is still required:
1. Pick a concrete instance strategy.
2. Replace the placeholder ctor/list stand-ins with real Lean container calls.
3. Add runtime tests for insert, lookup, contains, erase, and list conversion.
4. Re-evaluate whether the feature stays permanently narrow or becomes
   partially stabilizable.

Definition of done:
- Empty construction, insert, lookup, contains, erase, and list conversion
  reflect real Lean behavior.
- The docs no longer call the wrappers placeholders.
- Runtime tests cover at least one supported key matrix end to end.

## What Moved Forward

### `#[leanmodule]`

Status:
- Improved, but not fully complete.

What landed:
- explicit module metadata via `__leo3_module_metadata()`
- implicit export registration model for inline `#[leanfn]` items
- runtime tests for metadata shape
- real `cdylib` fixture build coverage in `leo3/tests/test_leanmodule_loading.rs`

What still remains:
- true downstream shared-library loading coverage is still limited
- richer export/registration metadata is still possible if Leo3 grows a fuller
  plugin/module story

### External objects

Status:
- Completed for the current conservative policy.

What landed:
- borrow-first helper APIs
- tests for the non-cloning path
- docs that make the policy explicit: trait-level `FromLean` stays clone-based,
  wrapper-level extraction is the preferred borrow-first path

### Architecture and contributor docs

Status:
- Completed for this phase.

What landed:
- `docs/architecture.md`
- `docs/contributing.md`
- cross-links from README and TESTING

## Secondary Follow-Ups

- add a real shared-library loading success-path test once the module-loading
  contract is widened enough to support it reliably
- continue tightening README / TESTING / phase docs when public behavior moves
- revisit container stabilization only after the FFI instance story is real
