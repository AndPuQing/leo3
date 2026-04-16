# Architecture

Leo3 is split into a small number of layers with intentionally narrow
responsibilities:

- `leo3-ffi`: raw C ABI bindings and inline runtime helpers
- `leo3-build-config`: Lean discovery and build-time config propagation
- `leo3-macros` + `leo3-macros-backend`: proc-macro entry points and expansion logic
- `leo3`: the safe user-facing runtime/token/conversion surface

## Runtime Model

Leo3 keeps Lean interaction in three lanes:

- one long-lived runtime worker thread performs one-time runtime bootstrap and
  serialized initialization-sensitive work
- caller threads use `with_lean()` or `ensure_lean_thread()` to attach safely
- Lean task APIs (`task`, `promise`, `tokio_bridge`) run on top of Lean's own
  task manager after the worker has initialized the runtime

This split exists because Lean's runtime and allocator assumptions are easier to
respect when bootstrap happens on a stable thread and callers only enter through
explicit attachment points.

## Ownership Model

The core pointer shapes are:

- `Lean<'l>`: proves the runtime is initialized for the current thread
- `LeanBound<'l, T>`: owned Lean object tied to that token
- `LeanBorrowed<'a, 'l, T>`: zero-cost borrowed view into an existing object
- `LeanRef<T>` / `LeanUnbound<T>`: ref-counted handles that can outlive a
  single token scope

Conversions are intentionally explicit. Leo3 keeps the built-in `IntoLean` /
`FromLean` matrix small, and uses wrapper-level APIs rather than broad implicit
trait magic when ownership rules would otherwise get fuzzy.

## Macro Boundary

The macros generate Rust shims, not a hidden second runtime:

- `#[leanfn]` builds FFI wrappers and function metadata
- `#[leanclass]` builds external-object shims plus Lean declaration metadata
- `#[leanmodule]` builds the module init entry point and module metadata

The macros rely on public `leo3` APIs instead of reaching into crate-private
 internals wherever practical. That keeps the runtime contract visible and makes
 the generated behavior easier to audit in tests.

## Module Model

Leo3's current module story has two parts:

- initialization: `#[leanmodule]` generates `initialize_*`
- export discovery: inline `#[leanfn]` items become the module's implicit export
  set, exposed through `__leo3_module_metadata()`

That is more explicit than the earlier "just generate init" phase, but it is
not yet a full shared-library registration system.

## Experimental Areas

The main intentionally narrow area is `experimental-containers`.

Those wrappers exist to reserve API shape and feature gating, not to claim that
Leo3 already has a stable container-semantic story. Any change in their actual
runtime behavior should be treated as stabilization work, not routine cleanup.
