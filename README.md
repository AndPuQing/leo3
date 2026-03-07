# Leo3: Rust Bindings for Lean4

![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/AndPuQing/leo3/ci.yml?style=flat-square&logo=github)
![Crates.io Version](https://img.shields.io/crates/v/leo3?style=flat-square&logo=rust)
![Crates.io Downloads (recent)](https://img.shields.io/crates/dr/leo3?style=flat-square)
[![dependency status](https://deps.rs/repo/github/AndPuQing/leo3/status.svg?style=flat-square)](https://deps.rs/repo/github/AndPuQing/leo3)
![Crates.io License](https://img.shields.io/crates/l/leo3?style=flat-square) ![Crates.io Size](https://img.shields.io/crates/size/leo3?style=flat-square)

Leo3 provides safe, ergonomic Rust bindings to the [Lean4](https://github.com/leanprover/lean4) theorem prover, inspired by [PyO3](https://github.com/PyO3/pyo3)'s architecture.

## Quick Start

Requires Lean 4.25.2 (install via [elan](https://github.com/leanprover/elan)).

```toml
[dependencies]
leo3 = "0.2.1"
```

```rust
use leo3::prelude::*;

fn main() -> LeanResult<()> {
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        let s = LeanString::new(lean, "Hello from Rust!")?;
        println!("{}", LeanString::to_str(&s)?);

        let n = LeanNat::from_usize(lean, 42)?;
        println!("{}", LeanNat::to_usize(&n)?);
        Ok(())
    })
}
```

## Cargo Features

Default features: **none**. The default build keeps the public surface intentionally
minimal: runtime initialization, smart pointers, core type wrappers/conversions,
closures, thunks, and synchronization helpers are always available.

| Feature | Enables |
|---------|---------|
| _default (none)_ | Core runtime/token APIs, conversions, closures, thunks, sync helpers, Lean type wrappers |
| `macros` | `#[leanfn]`, `#[leanclass]`, `#[leanmodule]`, `#[derive(IntoLean, FromLean)]` |
| `meta` | `leo3::meta::*` metaprogramming APIs |
| `io` | `leo3::io::*` IO / filesystem / process / environment helpers |
| `task` | `leo3::task`, `leo3::task_combinators`, `leo3::promise` |
| `module-loading` | `leo3::module::*` dynamic shared-library loading |
| `tokio` | `leo3::tokio_bridge::*` (implies `task`) |
| `runtime-tests` | Runtime-dependent integration tests (for development/CI) |

Example dependency declarations:

```toml
# Minimal core surface
leo3 = "0.2.1"

# Opt into specific subsystems
leo3 = { version = "0.2.1", features = ["macros", "meta", "task"] }
```

## Lean Discovery

Leo3 build scripts resolve Lean in a single shared order:

1. `LEO3_NO_LEAN=1` disables Lean detection and linking entirely.
2. `LEO3_CONFIG_FILE=/path/to/leo3-build-config.txt` provides an explicit key/value config.
3. Host discovery tries `LEO3_CROSS_*`, then `LEAN_HOME` (with optional `LEAN_LIB_DIR` / `LEAN_INCLUDE_DIR`), then `lake`, then `elan`, then `PATH`.

`leo3-ffi` is the authoritative detector. It exports the resolved config through Cargo's `DEP_LEAN4_LEO3_CONFIG`, and `leo3` consumes that propagated config so both crates always agree on Lean version cfgs and linker settings.

Explicit overrides are authoritative: if `DEP_LEAN4_LEO3_CONFIG`, `LEO3_CONFIG_FILE`, `LEO3_CROSS_*`, `LEAN_HOME`, `LEAN_LIB_DIR`, or `LEAN_INCLUDE_DIR` is set but invalid, Leo3 reports that error instead of silently falling back to a lower-priority source.

## Capability Overview

### Core Type Conversions

Bidirectional conversions between Rust and Lean types via `IntoLean` / `FromLean` traits:

| Rust | Lean | Wrapper |
|------|------|---------|
| `String`, `&str` | `String` | `LeanString` |
| `u8`–`u64`, `usize` | `UInt8`–`UInt64`, `USize` | `LeanUInt*` |
| `i8`–`i64`, `isize` | `Int8`–`Int64`, `ISize` | `LeanInt*` |
| `f32`, `f64` | `Float32`, `Float` | `LeanFloat32`, `LeanFloat` |
| `bool` | `Bool` | `LeanBool` |
| `char` | `Char` | `LeanChar` |
| `Vec<T>` | `Array` | `LeanArray` |
| `Option<T>` | `Option` | `LeanOption` |
| `Result<T, E>` | `Except` | `LeanExcept` |
| `(A, B)` | `Prod` / `Sigma` | `LeanProd` / `LeanSigma` |
| — | `List` | `LeanList` |
| — | `HashMap` / `HashSet` | `LeanHashMap` / `LeanHashSet` |
| — | `RBMap` | `LeanRBMap` |
| — | `Nat` / `Int` | `LeanNat` / `LeanInt` |
| — | `Sum`, `Fin`, `Subtype`, `BitVec`, `Range` | corresponding wrappers |

### Procedural Macros (`macros`)

`#[leanfn]` — Export Rust functions to Lean:

```rust
#[leanfn]
fn add(a: u64, b: u64) -> u64 {
    a + b
}
```

`#[leanclass]` — Expose Rust structs as Lean external classes with auto-generated FFI wrappers and Lean source declarations:

```rust
#[leanclass]
struct Counter { value: i64 }

#[leanclass]
impl Counter {
    fn new() -> Self { Counter { value: 0 } }
    fn get(&self) -> i64 { self.value }
    fn increment(&mut self) { self.value += 1; }
}
```

`#[derive(IntoLean)]` / `#[derive(FromLean)]` — Automatic conversion derive macros.

### Meta-Programming (`meta`)

Full access to Lean's kernel and elaborator:

- `LeanEnvironment` — Create and manage declaration environments
- `LeanExpr` — Build expressions (binders, applications, literals, lambda, forall)
- `LeanDeclaration` — Define axioms, definitions, and theorems
- `MetaMContext` — Type inference, type checking, definitional equality, proof validation
- Tactic support

### IO, Tasks, and Dynamic Loading

- `io`: console, filesystem, environment variables, process, and time helpers
- `task`: `LeanTask` / `LeanPromise` plus combinators (`join`, `race`, `select`, `timeout`)
- `module-loading`: `LeanModule` for loading compiled Lean shared libraries
- `tokio`: async bridge for Lean tasks
- Core (always available): `LeanClosure` and `LeanThunk`

## Architecture

```
leo3/
├── leo3/                   # Safe high-level abstractions
├── leo3-ffi/               # Raw FFI bindings to Lean4's C API
├── leo3-build-config/      # Build-time Lean4 detection and configuration
├── leo3-macros/            # Procedural macro entry points
├── leo3-macros-backend/    # Procedural macro implementations
└── leo3-ffi-check/         # FFI layout validation (à la pyo3-ffi-check)
```

### Design

- `Lean<'l>` token proves runtime initialization at compile-time
- `LeanBound<'l, T>` (lifetime-bound), `LeanRef<T>` (unbound), `LeanUnbound<T>` (thread-safe) smart pointers with automatic reference counting
- `#[repr(transparent)]` zero-cost wrappers
- Copy-on-write semantics for `&mut self` FFI methods
- Worker thread architecture for all Lean runtime calls (avoids mimalloc heap issues)
- Version support: Lean 4.20.0–4.30 with `#[cfg(lean_4_25)]` gates

### Comparison with PyO3

| PyO3 | Leo3 |
|------|------|
| `Python<'py>` | `Lean<'l>` |
| `Bound<'py, T>` | `LeanBound<'l, T>` |
| `Py<T>` | `LeanRef<T>` |
| `#[pyfunction]` | `#[leanfn]` |
| `#[pyclass]` | `#[leanclass]` |

## Development

See `TESTING.md` for the full tiered CI map and exact contributor workflows. Common local commands:

```bash
LEO3_NO_LEAN=1 cargo test --locked --workspace --exclude leo3 --lib
cargo test --locked -p leo3 --no-default-features --test test_features
LEO3_NO_LEAN=1 cargo test --locked -p leo3 --features macros --test test_compile_error
cargo test --locked --all-features --workspace
```

## License

MIT OR Apache-2.0

## Acknowledgments

- [PyO3](https://github.com/PyO3/pyo3) — Architectural inspiration
- [Lean4](https://github.com/leanprover/lean4) — The theorem prover Leo3 binds to
