# Leo3 Maturity Spec

## Status

Current implementation record as of 2026-04-15.

The maturity program defined in this document is no longer just a forward plan.
Its major decisions have been implemented across the 0.2.x line and broken out
into phase documents under `docs/`.

Current high-level status:

- Phase 0 is complete.
- Phases 1-3 are implemented on the stable default surface.
- Phases 4-5 have completed a first functional pass.
- Phases 6-7 are locked as the current conversion, `#[leanclass]`, docs, and
  test contract.
- Remaining work is follow-up hardening and future surface expansion, not
  unresolved foundation ambiguity.

## Purpose

This document records the maturity program that moved `leo3` from an early
"usable 0.x binding framework" toward a more disciplined Lean binding library
with:

- semantically honest public APIs
- one coherent runtime and threading model
- explicit macro error boundaries
- more faithful `#[leanclass]` behavior
- a documented conversion contract
- documentation and tests that act as interface checks

The reference point is not source-level parity with `pyo3`. Lean and Python
have different runtimes and extension models. The target is maturity parity:

- clear ownership and threading semantics
- complete and trustworthy stable APIs
- uniform error propagation across generated wrappers
- module and macro flows that are practical in downstream projects
- documentation and tests that validate intended usage

## Related Documents

- `docs/phase-1-public-api-honesty.md`
- `docs/phase-2-runtime-threading.md`
- `docs/phase-3-error-boundaries.md`
- `docs/phase-4-module-surface.md`
- `docs/phase-5-leanclass-semantics.md`
- `docs/phase-6-7-boundary-contract.md`
- `README.md`
- `TESTING.md`

## North Star

Leo3 should be the default Rust-side binding layer for Lean projects that need:

- safe runtime interaction with Lean values and environments
- stable FFI export and import patterns
- ergonomic proc macros for exposing Rust code to Lean
- predictable multithreaded behavior
- practical downstream authoring and testing workflows

## Non-Goals

The maturity program does not aim to provide:

- exact source-level parity with every `pyo3` macro or API
- every possible Lean metaprogramming abstraction in one pass
- generic support everywhere before core semantics are stable
- a package manager or distribution platform

## Design Principles

1. Public APIs must be semantically honest.
   If an API is exposed as a Lean wrapper, it must perform the real operation or
   be clearly gated or documented as experimental.

2. One semantic path beats many partial paths.
   Runtime initialization, module loading, and macro-generated bindings should
   converge on one consistent execution model.

3. Errors must cross boundaries explicitly.
   Generated wrappers should not use ad hoc recoverable-path `expect(...)` or
   silent fallback values.

4. Lean-side and Rust-side declarations must stay synchronized.
   Generated metadata, exported symbol names, and Lean declaration strings must
   describe actual runtime behavior.

5. Tests should validate intended usage, not only compilation.
   Compile-only checks remain useful, but the golden paths should be runnable
   where practical.

## Current State Summary

### Strengths

- Clear workspace layering across safe APIs, FFI, build config, macros, and FFI
  validation.
- Token-based runtime access model with `Lean<'l>` and lifetime-aware smart
  pointers.
- Canonical safe runtime entry path through `with_lean(...)`.
- Shared macro/runtime boundary helpers instead of one-off panic handling.
- Explicit conversion and `#[leanclass]` declaration contract.
- Better CI shape than many early-stage binding libraries, including doctests,
  UI tests, runtime integration tests, and FFI layout checks.

### Resolved Foundation Gaps

The original maturity plan targeted seven core problems. Their current status is
now:

1. Public placeholder APIs on the stable surface: addressed by explicit
   `experimental-containers` gating.
2. Split runtime initialization semantics: addressed by the unified
   `with_lean(...)` / `prepare_freethreaded_lean()` /
   `sync::ensure_lean_thread()` contract.
3. Mixed panic and result behavior in generated wrappers: addressed for the
   current macro families with shared boundary helpers.
4. Minimal `#[leanmodule]` parsing surface: improved with structured parsing and
   crate-path-aware generation.
5. Lossy `#[leanclass]` mutation semantics: addressed by preserving updated
   objects in the generated Lean-visible type.
6. Implicit conversion and extraction rules: addressed by the Phase 6/7
   boundary contract.
7. Docs and tests not acting as a contract: addressed by README, `TESTING.md`,
   doctests, runtime tests, and named UI matrices moving together.

### Remaining Gaps

The remaining work is real, but it is narrower than the original roadmap:

- `LeanHashMap`, `LeanHashSet`, and `LeanRBMap` are still experimental rather
  than stable.
- `#[leanmodule]` has a cleaner attribute surface, but not yet a richer module
  registration model.
- External-object ergonomics still lean on clone-based extraction for
  `FromLean`; borrow-first APIs exist, but the trait-level story is still
  intentionally conservative.
- Architecture and contributor docs can still go deeper even though the main
  user-facing contract is now written down.

## Phase Record

## Phase 0: Specification Lock-In

### Status

Complete.

### Outcome

- the maturity program is written down in this document
- phase-specific records exist in `docs/`
- the breaking-change rationale for the 0.x line is explicit

### Notes

This phase did its job: it created a stable decision frame before the larger API
and runtime cleanups landed.

## Phase 1: Public API Honesty

### Status

Implemented on the stable default surface.

### Outcome

- placeholder container wrappers were removed from the stable default surface
- `LeanHashMap`, `LeanHashSet`, and `LeanRBMap` now require
  `experimental-containers`
- README, crate docs, and feature tests all reflect that gating
- compile-time surface tests protect the decision

### Boundary

Phase 1 does not claim the experimental containers are complete. It claims only
that the default stable surface no longer presents them as complete.

### Record

See `docs/phase-1-public-api-honesty.md`.

## Phase 2: Unified Runtime and Threading Model

### Status

Implemented for the public runtime entry points.

### Outcome

- `with_lean(...)` is the canonical safe caller entry point
- `prepare_freethreaded_lean()` is eager worker startup, not caller-thread
  attachment
- `sync::ensure_lean_thread()` is the low-level attach-current-thread primitive
- module loading and macro-generated initialization use the same runtime model
- Leo3's internal TLS bookkeeping now matches the worker-thread reality

### Boundary

The runtime contract is coherent and documented. Further simplification is still
possible, but callers no longer have to infer contradictory initialization
semantics from multiple APIs.

### Record

See `docs/phase-2-runtime-threading.md`.

## Phase 3: Uniform Error Boundary and Panic Policy

### Status

Implemented for the current macro families.

### Outcome

- shared FFI boundary helpers now live in `leo3::__private`
- `#[leanclass]` wrappers use result-based try paths plus one outer panic
  boundary
- `#[lean_instance]` no longer uses silent empty-string fallbacks
- scalar-returning wrappers use an explicit abort-on-boundary-failure policy
  rather than pretending a Lean panic object can be returned in every case

### Boundary

This phase established one explicit policy for the macro families currently in
scope. It does not claim every future wrapper shape has already been designed.

### Record

See `docs/phase-3-error-boundaries.md`.

## Phase 4: Module Surface

### Status

First implementation pass completed.

### Outcome

- `#[leanmodule]` uses structured parsing instead of string manipulation
- module attributes now support the same crate-path customization style as other
  macros
- generated module initialization aligns with the Phase 2 runtime contract

### Remaining Work

Leo3 still does not define a richer exported-item registration model for
modules. Phase 4 therefore improved the brittle part of the surface without
claiming full module-system completion.

### Record

See `docs/phase-4-module-surface.md`.

## Phase 5: `leanclass` Semantic Completion

### Status

First implementation pass completed.

### Outcome

- `&mut self -> ()` remains a mutation-preserving path that returns the updated
  object to Lean
- `&mut self -> R` now returns `Prod Self R` so mutation state is not discarded
- generated Lean declaration strings more faithfully describe runtime behavior
- tests cover the mutation-preserving wrapper shape

### Remaining Work

The major semantic bug is fixed. More declaration-shape polish and broader test
coverage can still be added later.

### Record

See `docs/phase-5-leanclass-semantics.md`.

## Phase 6: Conversion and External Object Ergonomics

### Status

Current boundary contract written down and aligned across docs and tests.

### Outcome

- the supported built-in conversion matrix is explicit
- cost and ownership rules are documented
- external-object extraction is explicitly clone-based for `FromLean`
- borrow-based external access is documented as a separate API surface

### Boundary

Phase 6 currently acts as a contract lock, not a promise of maximal conversion
coverage. The intentionally small matrix is part of the maturity story.

### Record

See `docs/phase-6-7-boundary-contract.md`.

## Phase 7: Documentation and Test Maturity

### Status

Current boundary contract locked by docs and tests.

### Outcome

- README now documents the runtime model, conversion rules, and macro
  boundaries in one public place
- `TESTING.md` names the CI tiers and exact local commands
- doctests cover the public quick start and key macro/documentation paths
- UI tests lock intentionally unsupported `#[leanclass]` declaration shapes
- runtime and macro integration tests cover the main golden paths

### Boundary

Documentation maturity is now good enough to act as an interface contract.
That does not mean every possible runtime-dependent example is executable as a
standalone doctest.

### Record

See `docs/phase-6-7-boundary-contract.md` and `TESTING.md`.

## Cross-Cutting Engineering Rules

These rules remain in force after the initial maturity program:

1. No new placeholder public APIs on the stable default surface.
2. No new macro-generated `expect(...)` on recoverable paths.
3. New user-facing semantics require tests and docs in the same change.
4. Breaking behavior changes must update README, crate docs, UI snapshots, and
   end-to-end examples when relevant.

## Resolved Questions

The open questions in the original draft now have working answers:

1. Placeholder containers should be gated out of the stable default surface
   until they have real semantics. Leo3 chose gating, not premature promotion.
2. `with_lean(...)` should remain the canonical safe entry point.
   `sync::ensure_lean_thread()` is the lower-level explicit attachment API.
3. The canonical generated-wrapper policy is boundary-helper based: object
   wrappers route through shared panic boundaries, and scalar wrappers use an
   explicit stricter failure path.
4. Small amounts of Lean-side support code are acceptable when needed, but the
   current implemented surface prefers minimal support code plus explicit Rust-
   side and documentation contracts.
5. Trait-based metadata is not required for the current declaration surface.
   Leo3 instead locked a smaller explicit declaration grammar with UI tests.

## Release Context

The workspace is currently at `0.2.1`.

This maturity program should be read as "the core 0.2.x stabilization work that
already landed", not as a promise that Leo3 is ready for `1.0.0`.

Reasonable future release expectations are:

- `0.2.x`: continue hardening the now-explicit contracts
- `0.3.x`: widen stable surface only where semantics are already clear
- `1.0.0`: only after experimental containers, module surface, runtime
  semantics, macro semantics, and documentation/testing all feel intentionally
  stable rather than merely implemented

## Definition of Done

The original maturity program is considered fulfilled in the following sense:

- the stable default public API is semantically honest
- runtime and thread usage are coherent and documented
- macro-generated bindings share a predictable boundary policy
- module and class flows have a usable downstream story
- documentation and tests now describe and check the intended public contract

The remaining work before `1.0.0` is no longer "make the foundations coherent".
It is "decide what additional stable surface Leo3 is prepared to support
without weakening those foundations".
