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
leo3 = "0.1.6"
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

## Features

### Type Conversions

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

### Procedural Macros

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

### Meta-Programming

Full access to Lean's kernel and elaborator:

- `LeanEnvironment` — Create and manage declaration environments
- `LeanExpr` — Build expressions (binders, applications, literals, lambda, forall)
- `LeanDeclaration` — Define axioms, definitions, and theorems
- `MetaMContext` — Type inference, type checking, definitional equality, proof validation
- Tactic support

### IO & Runtime

- IO operations: console, filesystem, environment variables, process, time
- `LeanClosure` — Create and apply Lean closures from Rust
- `LeanTask` / `LeanPromise` — Parallel computation with combinators (`join`, `race`, `select`, `timeout`)
- `LeanModule` — Dynamic loading of compiled Lean shared libraries
- Tokio bridge for async integration
- `LeanThunk` — Lazy evaluation

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

```bash
cargo test                        # Full test suite (requires Lean 4.25.2)
cargo test --test meta_basic      # Specific test
LEO3_NO_LEAN=1 cargo test --lib   # Compile-only, no Lean runtime
```

## License

MIT OR Apache-2.0

## Acknowledgments

- [PyO3](https://github.com/PyO3/pyo3) — Architectural inspiration
- [Lean4](https://github.com/leanprover/lean4) — The theorem prover Leo3 binds to
