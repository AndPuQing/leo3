# Leo3: Rust Bindings for Lean4

![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/AndPuQing/leo3/ci.yml?style=flat-square&logo=github)
![Crates.io Version](https://img.shields.io/crates/v/leo3?style=flat-square&logo=rust)
![Crates.io Downloads (recent)](https://img.shields.io/crates/dr/leo3?style=flat-square)
[![dependency status](https://deps.rs/repo/github/AndPuQing/leo3/status.svg?style=flat-square)](https://deps.rs/repo/github/AndPuQing/leo3)
![Crates.io License](https://img.shields.io/crates/l/leo3?style=flat-square) ![Crates.io Size](https://img.shields.io/crates/size/leo3?style=flat-square)


Leo3 provides safe, ergonomic Rust bindings to the Lean4 theorem prover, inspired by [PyO3](https://github.com/PyO3/pyo3)'s architecture for Python-Rust bindings.

## Project Status

⚠️ **Work in Progress** - Leo3 is in early development. The core architecture is established, but many features are not yet implemented.

## Architecture

Leo3 is organized as a workspace with multiple crates:

```
leo3/
├── leo3                  # Main crate - high-level safe abstractions
├── leo3-ffi              # Raw FFI bindings to Lean4's C API
├── leo3-build-config     # Build-time Lean4 detection and configuration
├── leo3-macros           # Procedural macro entry points
└── leo3-macros-backend   # Procedural macro implementations
```

### Design Philosophy

Leo3 follows PyO3's proven architecture patterns:

1. **Layered Abstraction**: Clear separation between raw FFI, safe wrappers, and user-facing API
2. **Zero-Cost**: `#[repr(transparent)]` wrappers with compile-time safety
3. **Lifetime Safety**: The `Lean<'l>` token ensures Lean runtime initialization at compile-time
4. **Automatic Memory Management**: Smart pointers handle reference counting
5. **Macro-Driven Ergonomics**: Procedural macros reduce boilerplate

## Core Concepts

### The `Lean<'l>` Token

All Lean operations require a `Lean<'l>` token, proving the runtime is initialized:

```rust
use leo3::prelude::*;

fn process_data<'l>(lean: Lean<'l>) -> LeanResult<()> {
    let s = LeanString::new(lean, "Hello, Lean!")?;
    Ok(())
}
```

### Smart Pointers

Leo3 provides two primary smart pointer types:

- **`LeanBound<'l, T>`**: Tied to `Lean<'l>` lifetime, used for most operations
- **`LeanRef<T>`**: Can cross initialization boundaries, useful for storage

Both handle reference counting automatically.

### Type System

Lean types are wrapped in safe Rust types with automatic conversions:

```rust
use leo3::conversion::{IntoLean, FromLean};

// Strings
let s = LeanString::new(lean, "Hello")?;
let rust_str = LeanString::to_str(&s)?;

// Natural numbers
let n = LeanNat::from_usize(lean, 42)?;
let value = LeanNat::to_usize(&n)?;

// Signed integers (i8, i16, i32, i64, isize)
let rust_int: i32 = -42;
let lean_int = rust_int.into_lean(lean)?;
let back: i32 = FromLean::from_lean(&lean_int)?;

// Floating-point (f32, f64)
let rust_float: f64 = 3.14159;
let lean_float = rust_float.into_lean(lean)?;
let back: f64 = FromLean::from_lean(&lean_float)?;

// Option<T>
let rust_opt: Option<u64> = Some(42);
let lean_opt = rust_opt.into_lean(lean)?;
let back: Option<u64> = FromLean::from_lean(&lean_opt)?;

// Result<T, E>
let rust_result: Result<i32, String> = Ok(42);
let lean_result = rust_result.into_lean(lean)?;
let back: Result<i32, String> = FromLean::from_lean(&lean_result)?;

// Arrays and vectors
let vec = vec![1, 2, 3, 4, 5];
let lean_arr = vec.into_lean(lean)?;
let back: Vec<i32> = FromLean::from_lean(&lean_arr)?;
```

## Installation

**Note**: Lean4 must be installed on your system. Leo3 will attempt to detect it via:
1. `LEAN_HOME` or `ELAN_HOME` environment variables
2. `lake` command
3. `elan` toolchain manager
4. `lean` in PATH

Add to your `Cargo.toml`:

```toml
[dependencies]
leo3 = "0.1.0"
```

## Example Usage

```rust
use leo3::prelude::*;

#[leanfn]
fn add(a: u64, b: u64) -> u64 {
    a + b
}

fn main() -> LeanResult<()> {
    // Initialize Lean runtime
    leo3::prepare_freethreaded_lean();

    leo3::with_lean(|lean| {
        // Create Lean objects
        let s = LeanString::new(lean, "Hello from Rust!")?;
        println!("Created string: {}", LeanString::to_str(&s)?);

        let n = LeanNat::from_usize(lean, 100)?;
        println!("Created nat: {}", LeanNat::to_usize(&n)?);

        Ok(())
    })
}
```

## Examples

The `leo3/examples/` directory contains runnable demos:

| Example | Description |
|---------|-------------|
| [`io_monad`](leo3/examples/io_monad.rs) | IO monad basics — wrap side-effects in Lean's IO type |
| [`proof_construction`](leo3/examples/proof_construction.rs) | Build and type-check kernel proofs programmatically |
| [`leanmodule_export`](leo3/examples/leanmodule_export.rs) | `#[leanmodule]` macro — generate Lean4 module init functions |
| [`async_task_promise`](leo3/examples/async_task_promise.rs) | Task/promise combinators — `join`, `select`, `timeout` |

Run any example with:

```bash
cargo run --example <name>          # e.g. cargo run --example leanmodule_export
```

## Feature Flags

- **`macros`** (default): Enable procedural macros (`#[leanfn]`, `#[leanclass]`, etc.)

## Comparison with PyO3

Leo3 adapts PyO3's architecture for Lean4:

| PyO3 Concept | Leo3 Equivalent | Notes |
|--------------|-----------------|-------|
| `Python<'py>` | `Lean<'l>` | Runtime initialization token |
| `Bound<'py, T>` | `LeanBound<'l, T>` | Lifetime-bound smart pointer |
| `Py<T>` | `LeanRef<T>` | Unbound smart pointer |
| `#[pyfunction]` | `#[leanfn]` | Function export macro |
| `#[pyclass]` | `#[leanclass]` | Class export macro |
| `PyObject` | `lean_object` | Base object type |
| GIL | Lean runtime | No equivalent (Lean has no GIL) |

### Key Differences from PyO3

1. **No GIL**: Lean4 doesn't have a Global Interpreter Lock, simplifying thread safety
2. **Different Memory Model**: Lean uses reference counting without generational GC
3. **Theorem Proving Focus**: Leo3 will support proof objects and tactics
4. **Dependent Types**: Future support for Lean's dependent type system

## Roadmap

### Completed ✅
- [x] `#[leanfn]` macro implementation
- [x] String parameter passing (String, &str ↔ LeanString)
- [x] Unsigned integer conversions (u8, u16, u32, u64, usize ↔ UInt8, UInt16, UInt32, UInt64, USize)
- [x] Array parameter passing (Vec<T> ↔ LeanArray)
- [x] Signed integer conversions (i8, i16, i32, i64, isize ↔ Int8, Int16, Int32, Int64, ISize)
- [x] Floating-point conversions (f32, f64 ↔ LeanFloat)
- [x] Option type conversions (Option<T> ↔ LeanOption)
- [x] Result type conversions (Result<T, E> ↔ LeanExcept)
- [x] `#[leanclass]` for Rust structs as Lean classes (with Lean source code generation)
- [x] `#[leanmodule]` for module creation
- [x] Async support (task/promise combinators)
- [x] CI/CD pipeline
- [x] Example projects

### In Progress 🚧
- [ ] Complete FFI bindings (more Lean API functions)
- [ ] Error handling improvements

### Planned 📋
- [ ] IO monad support
- [ ] Proof object support
- [ ] Tactic integration
- [ ] Environment and context management
- [ ] Documentation generation
- [ ] Integration tests with actual Lean4

## Development

### Building

```bash
# Build all crates
cargo build

# Build specific crate
cargo build -p leo3-ffi

# Run tests
cargo test
```

### Testing

Currently, most tests are unit tests. Integration tests requiring a Lean4 installation will be added.

### Contributing

Contributions are welcome! Areas that need work:
- Completing FFI bindings
- Implementing macro code generation
- Adding more type wrappers
- Documentation
- Examples
- Tests

## Acknowledgments

- **[PyO3](https://github.com/PyO3/pyo3)**: The architectural inspiration for Leo3
- **[Lean4](https://github.com/leanprover/lean4)**: The theorem prover Leo3 binds to

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Related Projects

- [PyO3](https://github.com/PyO3/pyo3) - Rust bindings for Python
- [Lean4](https://github.com/leanprover/lean4) - The Lean theorem prover
- [LeanInk](https://github.com/leanprover/LeanInk) - Lean documentation tool
