# Leo3 Remaining Work Checklist

Status snapshot as of 2026-04-16.

This file tracks the maturity gaps that are still meaningfully open after the
current hardening pass. It is not a re-listing of every future enhancement
idea, and it should not regress into a stale copy of the older roadmap.

## What Changed Since the Old Checklist

The earlier four-item list no longer matches the codebase:

- `#[leanmodule]` now has structured parsing, crate-path-aware generation, and
  metadata-driven implicit export discovery through
  `__leo3_module_metadata()`.
- macro producers now share a real workspace semantic IR/analyzer crate
  (`leo3-binding-ir`) instead of ad hoc name-only metadata.
- external objects now have an explicit borrow-first wrapper API through
  `borrow()`, `try_get_mut()`, and `try_take_inner()`.
- architecture and contributor docs now exist and are linked from the main
  maintenance docs.

That means the main unresolved work is narrower than before.

## Active Remaining Work

### P1: Experimental containers still need broader stabilization work

Status:

- Narrow implementation completed.
- Still correctly gated behind `experimental-containers`.

Why this is still the top priority:

- `LeanHashMap`, `LeanHashSet`, and `LeanRBMap` now all have real
  runtime-backed implementations for a narrow key matrix.
- The remaining work is no longer "replace placeholders"; it is broader matrix
  support, durability, and eventual stabilization policy.

Code evidence:

- `leo3/src/types/containers/hashmap.rs`
- `leo3/src/types/containers/hashset.rs`
- `leo3/src/types/containers/rbmap.rs`
- `leo3/src/types/containers/README.md`
- `leo3-ffi/src/hashmap.rs`
- `leo3-ffi/src/hashset.rs`
- `leo3-ffi/src/rbmap.rs`

What is still required:

1. Decide whether the current narrow supported key matrix is enough to stabilize
   in part, or whether the feature should stay experimental until widened.
2. Broaden the supported key matrix only when the runtime instance source stays
   explicit and testable.
3. Keep the container docs aligned with the exact supported matrix instead of
   drifting back to vague "generic support" language.

Recommended implementation order:

1. Add more supported key families only when their `DecidableEq` / `Hashable` /
   compare sources are concrete exported closures or boxed functions.
2. Expand runtime tests before widening public claims.
3. Re-evaluate whether stabilization should stay intentionally narrow or widen.

Definition of done:

- The supported key matrix is documented, tested, and no longer likely to
  surprise downstream users.
- The feature-gated surface either stabilizes in a narrow form or has a clearly
  documented reason to remain experimental.
- Runtime tests cover the supported paths against actual Lean semantics across
  all three container families.

### P2: Real module-loading success-path coverage is still missing

Status:

- Partially improved, but not complete.

What already landed:

- `#[leanmodule]` metadata tests cover the implicit export model.
- runtime tests cover the generated init symbol and thread-attachment behavior.
- `leo3/tests/test_leanmodule_loading.rs` builds a real downstream `cdylib`
  fixture.

What is still missing:

- a test that actually loads that built fixture through
  `leo3::module::LeanModule::load(...)`
- symbol lookup through `get_function(...)`
- a successful call into at least one exported `#[leanfn]` wrapper from the
  loaded module

Current blocker discovered during attempted completion:

- the current `LeanModule::load(...)` success path aborts when the built fixture
  is loaded after Leo3 has already completed runtime initialization, with Lean
  reporting `Failed to register option: Options can only be registered during initialization`
- this is a real runtime / plugin-loading contract gap, not just a missing test
  assertion

Code evidence:

- `leo3/src/module.rs`
- `leo3/tests/test_leanmodule.rs`
- `leo3/tests/test_leanmodule_loading.rs`
- `leo3/tests/fixtures/leanmodule_runtime_fixture/src/lib.rs`

Definition of done:

- the test fixture is built, loaded, initialized, queried for an exported
  function, and called successfully through the public module-loading API
- failures in that flow would clearly localize whether the issue is fixture
  generation, dynamic loading, symbol naming, or call conversion

## Closed For The Current Policy

### External objects

Status:

- Closed for the current conservative contract.

What landed:

- borrow-first helper APIs
- runtime coverage for the non-cloning wrapper path
- docs that make the ownership split explicit

What is intentionally not treated as open work right now:

- trait-level `FromLean` remains clone-based
- borrow-first extraction remains a wrapper-level API, not a trait-level one

Re-open this item only if Leo3 deliberately changes the extraction contract.

### Architecture and contributor docs

Status:

- Closed for this phase.

What landed:

- `docs/architecture.md`
- `docs/contributing.md`
- cross-links from `README.md` and `TESTING.md`

These docs can always deepen later, but their absence is no longer a maturity
gap.

## Future Expansion, Not Current Blockers

- richer module-registration metadata beyond today's implicit inline
  `#[leanfn]` export set
- a broader external-object extraction contract, if Leo3 ever decides to widen
  beyond the current clone-based `FromLean` rule
- container stabilization for a wider type matrix after one narrow supported
  path is real

## Maintenance Rule

When one of the active items above moves, update these surfaces together:

- `README.md`
- `TESTING.md`
- `docs/contracts.md`
- runtime tests or UI tests that define the current contract
- this checklist
