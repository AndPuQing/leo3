# Leo3 Maturity Spec

## Status

Draft v0.1

## Purpose

This document defines a staged plan to move `leo3` from its current "usable 0.x binding framework" state toward a mature Lean binding library with clearer semantics, fewer placeholder APIs, stronger macro ergonomics, and a more coherent runtime model.

The reference point is not literal feature parity with `pyo3`, because Lean and Python have different runtimes and extension models. The reference point is product maturity parity:

- clear ownership and threading semantics
- complete and trustworthy public APIs
- uniform error propagation
- module and macro flows that are practical in real downstream projects
- documentation and tests that validate the intended usage paths

## Problem Statement

`leo3` already has strong foundations:

- layered architecture (`leo3`, `leo3-ffi`, macros, build-config, ffi-check)
- token-based access model (`Lean<'l>`)
- smart pointer model (`LeanBound`, `LeanRef`, `LeanUnbound`)
- runtime worker design for sensitive Lean initialization paths
- proc macros for functions, classes, modules, derives, and Lean typeclass hooks
- meaningful runtime and compile-fail test coverage

However, several high-level APIs and semantics are still incomplete or inconsistent:

- some public container wrappers are placeholder implementations
- runtime initialization semantics are split across multiple paths
- generated macro wrappers do not share one error model
- `#[leanmodule]` is minimal and not yet a true module registration system
- `#[leanclass]` semantics are incomplete for some mutation and conversion paths
- documentation coverage is broad, but many examples are still ignored instead of executable

## North Star

Leo3 should become the default Rust-side binding layer for Lean projects that need:

- safe runtime interaction with Lean values and environments
- stable FFI export/import patterns
- ergonomic proc macros for exposing Rust code to Lean
- predictable multithreaded behavior
- practical downstream authoring and testing workflows

## Non-Goals

The following are explicitly out of scope for this spec:

- exact source-level parity with every `pyo3` macro or API
- solving all possible Lean metaprogramming abstractions in one pass
- implementing generic support everywhere before core semantics are stable
- building a generalized package manager or distribution platform

## Design Principles

1. Public APIs must be semantically honest.
   If an API is exposed as a Lean wrapper, it must either perform the real operation or be clearly gated/removed from stable surface.

2. One semantic path beats many partial paths.
   Runtime initialization, module loading, and macro-generated bindings must converge on one consistent execution model.

3. Errors must cross boundaries explicitly.
   Generated wrappers should not panic or silently degrade on recoverable failures.

4. Lean-side and Rust-side declarations must remain synchronized.
   Generated metadata, extern names, signatures, and registration hooks must reflect actual runtime behavior.

5. Tests should validate intended usage, not only compilation.
   Compile-only docs are useful, but the golden paths must be executable where practical.

## Current State Summary

### Strengths

- Clear crate layering and ownership boundaries.
- Reasonable smart pointer architecture modeled after modern binding libraries.
- Early support for runtime, module loading, meta APIs, async/task, and macros.
- CI structure is already better than many early-stage libraries.

### Main Gaps

1. Public placeholder APIs exist in stable surface.
2. Thread/runtime initialization semantics are not fully unified.
3. Macro-generated code uses mixed panic and result behavior.
4. Module initialization is not yet a complete downstream story.
5. Some Lean declaration/codegen paths are lossy.
6. External object ergonomics are still low-level.
7. Documentation execution ratio is still too low.

## Phase Plan

## Phase 0: Specification Lock-In

### Goal

Create a stable implementation target before changing behavior.

### Deliverables

- this spec
- a tracked phase checklist derived from this spec
- issue or task breakdown per phase

### Exit Criteria

- team agrees on phase ordering
- breaking-change policy for the next releases is explicit

## Phase 1: Public API Honesty

### Goal

Remove or clearly isolate public APIs whose semantics are not real yet.

### Scope

- audit all public APIs for placeholder behavior
- decide for each placeholder item:
  - implement now
  - gate behind unstable/internal feature
  - document as experimental
  - remove from public surface until real

### Priority Targets

- `LeanHashMap`
- `LeanHashSet`
- `LeanRBMap`
- any helper that returns placeholder values, fake structures, or lossy stand-ins

### Required Outcomes

- no stable public API should intentionally lie about Lean behavior
- placeholder container APIs are either real or clearly marked and gated

### Acceptance Criteria

- grep-based placeholder audit has no unresolved stable-surface placeholder hits
- README and docs do not advertise incomplete semantics as production-ready
- test suite includes explicit checks for the revised public status

### Risks

- temporary reduction in exposed surface may feel like regression
- real container support depends on typeclass instance strategy

### Notes

If full generic container support is too large for this phase, the correct move is to narrow scope honestly rather than keep fake implementations public.

## Phase 2: Unified Runtime and Threading Model

### Goal

Make runtime access semantics coherent and explainable.

### Scope

- define exact contract for:
  - `prepare_freethreaded_lean()`
  - `with_lean(...)`
  - `ensure_lean_thread()`
  - module loading path
  - macro-generated initialization path
- eliminate contradictory initialization behavior
- document the allowed thread transitions for:
  - caller threads
  - worker thread
  - Lean task execution
  - Tokio bridge

### Required Outcomes

- there is one canonical initialization model
- `with_lean` is either made safe-by-construction or clearly separated from a lower-level unsafe path
- `#[leanmodule]` and `LeanModule::load` follow the same runtime assumptions

### Acceptance Criteria

- a new runtime model section exists in crate docs and README
- dedicated tests cover:
  - calling from main thread
  - calling from spawned threads
  - calling after `ensure_lean_thread`
  - module loading path
  - task/tokio path
- no public path depends on undocumented `assume_initialized()` usage patterns

### Risks

- any change here may expose latent assumptions in current tests
- runtime worker invariants may need internal refactors before the public API becomes cleaner

## Phase 3: Uniform Error Boundary and Panic Policy

### Goal

Make generated bindings fail in a controlled, inspectable way.

### Scope

- define one error conversion policy for proc-macro generated extern wrappers
- remove `.expect(...)` from generated FFI wrappers
- remove silent lossy fallbacks such as "return empty string on conversion failure"
- standardize panic boundary handling across:
  - `#[leanfn]`
  - `#[leanclass]`
  - `#[lean_instance]`
  - future module wrappers

### Required Outcomes

- recoverable failures become Lean-visible error objects or structured panic objects according to one policy
- internal panics are caught at extern boundaries
- downstream users can reason about failure behavior without reading macro output

### Acceptance Criteria

- generated code contains no recoverable-path `expect`/`unwrap`
- test suite covers conversion failure, user panic, internal error, and type mismatch across all macro families
- error messages are stable enough for snapshot testing where appropriate

### Risks

- Lean-side error representation may need additional support helpers
- changing failure behavior may require updating current macro tests

## Phase 4: Module System Completion

### Goal

Turn `#[leanmodule]` into a real downstream module authoring story.

### Scope

- replace stringly attribute parsing with proper structured parsing
- define what a Lean module means in `leo3`
- support explicit registration of exported functions/classes/instances
- make generated initialization logic compatible with runtime policy from Phase 2
- document recommended Rust + Lean project layout

### Required Outcomes

- `#[leanmodule]` is not just an `initialize_*` symbol generator
- module initialization reflects exported items intentionally
- downstream crate authors have a documented and testable integration path

### Acceptance Criteria

- macro supports robust parsing and useful compile errors
- end-to-end example covers:
  - a module
  - exported functions
  - exported class
  - initialization from Lean/runtime side
- module-loading tests validate realistic usage, not only symbol presence

### Risks

- may require additional metadata representation
- may require small Lean-side support code or conventions

## Phase 5: `leanclass` Semantic Completion

### Goal

Make Rust external classes behave predictably as Lean-facing objects.

### Scope

- define exact ownership rules for:
  - `&self`
  - `&mut self`
  - `self`
- fix `&mut self` plus non-unit return semantics
- improve Lean signature generation so generated declarations match real runtime behavior
- review `ExternalClass` lifecycle hooks, GC hooks, and nested Lean object marking needs
- improve downcast and borrow ergonomics

### Required Outcomes

- no mutation path discards state silently
- generated Lean declarations are faithful
- class wrappers support common downstream patterns without raw-pointer reasoning

### Acceptance Criteria

- targeted tests for:
  - borrowed methods
  - mutating methods
  - consuming methods
  - methods returning `Self`
  - methods returning values after mutation
- generated declaration tests include more than primitive scalar cases

### Risks

- exact Lean-side encoding of mutable semantics may require explicit design tradeoffs
- richer declaration mapping may depend on trait-based type metadata

## Phase 6: Conversion and External Object Ergonomics

### Goal

Raise the abstraction level for common Rust-to-Lean and Lean-to-Rust flows.

### Scope

- review conversion trait design for future extensibility
- reduce forced `Clone` extraction patterns where borrow-based access is more appropriate
- add more structured conversions for common types where semantics are stable
- define which conversions are zero-copy, clone-based, or allocative

### Required Outcomes

- conversion docs state cost and ownership model
- external object extraction has a better story than "clone the Rust value"
- derive macros align with actual runtime expectations and failure modes

### Acceptance Criteria

- new docs table maps conversion category to cost and guarantees
- examples show borrow-based and owned extraction patterns
- benchmark coverage exists for hot-path conversions that matter

### Risks

- some ergonomic improvements may need new wrapper types
- overly broad conversion support can create long-term maintenance burden

## Phase 7: Documentation and Test Maturity

### Goal

Ensure the documented golden paths are runnable and trusted.

### Scope

- convert as many ignored doctests as practical into compile or runtime-tested examples
- document the canonical workflows:
  - standalone runtime use
  - exporting Rust functions to Lean
  - defining external classes
  - module loading
  - thread-safe object handoff
  - task/tokio integration
- add a contributor-facing architecture guide for runtime and macro semantics

### Required Outcomes

- docs become a tested interface contract
- common downstream paths have one recommended example each

### Acceptance Criteria

- ignored doctest count is materially reduced
- README quick start, macro quick start, and module quick start are tested
- architecture docs explain why the runtime worker exists and when `ensure_lean_thread` is required

### Risks

- some runtime-dependent docs may remain non-executable without dedicated fixtures
- examples can rot unless explicitly tied to CI

## Cross-Cutting Engineering Rules

The following rules apply across all phases:

1. No new placeholder public APIs.
2. No new macro-generated `expect` on recoverable paths.
3. New user-facing semantics require tests and docs in the same change.
4. Breaking behavior changes must update:
   - README
   - crate docs
   - trybuild/UI snapshots when relevant
   - end-to-end examples when relevant

## Proposed Execution Order

Recommended implementation order:

1. Phase 1: Public API honesty
2. Phase 2: Unified runtime/threading model
3. Phase 3: Uniform error boundary
4. Phase 5: `leanclass` semantic completion
5. Phase 4: Module system completion
6. Phase 6: Conversion and external object ergonomics
7. Phase 7: Documentation and test maturity

Reasoning:

- placeholder APIs and runtime inconsistency are the highest-risk foundation issues
- `leanclass` and `leanmodule` should be rebuilt on top of the runtime and error model, not before
- documentation should finalize the stabilized semantics rather than document moving targets too early

## Release Strategy

### Suggested Versioning

- `0.2.x`: stabilization work may still include breaking changes with explicit release notes
- `0.3.0`: target release for runtime model, error model, and API honesty cleanup
- `0.4.0`: target release for stronger module/class ergonomics and richer docs
- `1.0.0`: only after container semantics, runtime semantics, macro semantics, and documentation/testing are all coherent and intentionally stable

### Breaking-Change Policy Before 1.0

Breaking changes are acceptable when they:

- remove dishonest placeholder behavior
- unify contradictory runtime semantics
- replace panic-prone generated behavior with structured failure behavior

They must still be documented clearly and accompanied by migration notes.

## Open Questions

These questions should be resolved during implementation, not before Phase 1 starts:

1. Should placeholder containers be temporarily gated out, or should we implement a minimal real subset first?
2. Should `with_lean` remain safe, or should a lower-level unsafe entry point become explicit?
3. What is the canonical Lean-visible error representation for generated wrappers?
4. How much Lean-side support code is acceptable for a complete module/container story?
5. Do we want trait-based metadata for better Lean declaration generation?

## Definition of Done

This spec is considered fulfilled when:

- stable public APIs are semantically honest
- runtime and thread usage are coherent and documented
- macro-generated bindings share one predictable error boundary
- module and class flows support real downstream projects
- documentation demonstrates the intended workflows and is substantially tested

At that point, `leo3` should no longer feel like a promising prototype. It should feel like a dependable binding layer.
