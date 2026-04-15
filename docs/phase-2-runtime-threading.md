# Phase 2: Runtime and Threading Model

## Status

Implemented for the public runtime entry points.

## Goal

Make Leo3's public runtime entry points coherent:

- one process-wide runtime worker model
- one caller-thread attachment model
- one module initialization model

## Decisions Made

### 1. `with_lean()` is the canonical safe caller entry point

`with_lean()` now:

- ensures the runtime worker exists
- attaches the current thread
- only then constructs `Lean<'l>`

This replaces the older behavior where `with_lean()` assumed the caller had
already performed all initialization correctly.

### 2. `prepare_freethreaded_lean()` is eager startup, not caller-thread attach

`prepare_freethreaded_lean()` now has a narrower, clearer meaning:

- start the shared runtime worker eagerly
- do not attach the caller thread by itself

This keeps it useful for startup prewarming without pretending it has attached
the thread that called it.

### 3. `ensure_lean_thread()` is the low-level "attach current thread" primitive

`ensure_lean_thread()` now also guarantees the process-wide runtime worker
exists before attaching the caller thread.

That means low-level thread code no longer needs to remember a separate
process-wide `prepare_freethreaded_lean()` call first.

### 4. Worker-thread bookkeeping is now reflected in Leo3 TLS state

The runtime worker directly initializes Lean, so Leo3 now marks that worker as
initialized in its own thread-local bookkeeping as well.

This prevents Leo3's internal view of thread attachment from diverging from
what the worker has already done.

### 5. Module initialization uses the same runtime path

The following now align with the same runtime/thread model:

- `with_lean()`
- `sync::ensure_lean_thread()`
- `module::LeanModule::load(...)`
- macro-generated `initialize_*` entry points from `#[leanmodule]`

The `#[leanmodule]` code path no longer calls Lean initialization primitives
directly on the caller thread.

## New Contract

### Process-wide

- The runtime worker is created lazily on first safe entry or eagerly by
  `prepare_freethreaded_lean()`.

### Per-thread

- A caller thread becomes Leo3-ready by calling `with_lean()` or
  `sync::ensure_lean_thread()`.

### Module loading

- `LeanModule::load(...)` is responsible for making the caller thread ready
  before creating worlds and invoking module init symbols.

### Generated module init symbols

- `initialize_*` entry points produced by `#[leanmodule]` align with the same
  runtime path instead of open-coding direct FFI initialization.

## Validation Performed

- `cargo test --locked -p leo3 --features runtime-tests --test basic`
- `cargo test --locked -p leo3 --features runtime-tests --test test_thread_safety`
- `cargo test --locked -p leo3 --features "macros,runtime-tests" --test test_leanmodule`
- `cargo test --locked -p leo3 --doc --no-default-features`
- `cargo test --locked -p leo3 --doc --features "macros,task,tokio,module-loading"`

## Follow-Up Work Still Open

1. document the runtime model in more architectural depth
2. review whether more task/module APIs should be simplified around the same model
3. decide whether a more explicit public "attach" name should eventually replace
   or complement `ensure_lean_thread()`
