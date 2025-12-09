# Leo3: Rust Bindings for Lean4

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

Lean types are wrapped in safe Rust types:

```rust
// Strings
let s = LeanString::new(lean, "Hello")?;
let rust_str = LeanString::to_str(&s)?;

// Natural numbers
let n = LeanNat::from_usize(lean, 42)?;
let value = LeanNat::to_usize(&n)?;

// Arrays
let arr = LeanArray::new(lean)?;
let size = LeanArray::size(&arr);
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
| `#[pyclass]` | `#[leanclass]` | Class export macro (planned) |
| `PyObject` | `lean_object` | Base object type |
| GIL | Lean runtime | No equivalent (Lean has no GIL) |

### Key Differences from PyO3

1. **No GIL**: Lean4 doesn't have a Global Interpreter Lock, simplifying thread safety
2. **Different Memory Model**: Lean uses reference counting without generational GC
3. **Theorem Proving Focus**: Leo3 will support proof objects and tactics
4. **Dependent Types**: Future support for Lean's dependent type system

## Roadmap

### In Progress 🚧
- [ ] Complete FFI bindings (more Lean API functions)
- [ ] Array parameter passing (Vec, arrays ↔ LeanArray)
- [ ] Error handling improvements

### Planned 📋
- [ ] IO monad support
- [ ] Additional type conversions (i8, i16, i32, i64, f32, f64, Option, Result)
- [ ] `#[leanclass]` for Rust structs as Lean classes
- [ ] `#[leanmodule]` for module creation
- [ ] Proof object support
- [ ] Tactic integration
- [ ] Environment and context management
- [ ] Async support
- [ ] Documentation generation
- [ ] Integration tests with actual Lean4
- [ ] CI/CD pipeline
- [ ] Example projects

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
