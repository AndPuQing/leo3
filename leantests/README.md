# Lean Integration Tests

This directory contains integration tests for Rust ↔ Lean interoperability.

## Purpose

These tests verify that:
1. Rust can call Lean functions
2. Lean can call Rust functions
3. Data is correctly marshalled between Rust and Lean
4. Complex interactions work correctly

## Structure

```
leantests/
├── lean/          # Lean4 source code
│   ├── Basic.lean     # Basic Lean functions for testing
│   ├── Math.lean      # Mathematical functions
│   └── lakefile.lean  # Lake build configuration
├── src/           # Rust test code
│   ├── main.rs        # Test runner
│   └── tests/         # Individual test modules
└── build.rs       # Build script to compile Lean code
```

## Requirements

- **Lean4** must be installed and in PATH
- **Lake** (Lean's build tool) must be available
- Lean libraries must be properly linked to the Rust binary

## Running Tests

```bash
# Build Lean code and run tests
cargo test --package leantests

# Run specific test
cargo test --package leantests test_basic_arithmetic
```

## Writing Tests

### 1. Write Lean Code

Create a Lean file in `lean/`:

```lean
-- lean/Math.lean
def add (a b : Nat) : Nat := a + b
def multiply (a b : Nat) : Nat := a * b
```

### 2. Export for FFI

Mark functions for export:

```lean
@[export add_impl]
def add (a b : Nat) : Nat := a + b
```

### 3. Write Rust Test

Create test in `src/tests/`:

```rust
// src/tests/math_tests.rs
use leo3::prelude::*;

#[test]
fn test_lean_add() {
    leo3::with_lean(|lean| {
        // Call Lean function
        let result = call_lean_add(lean, 2, 3)?;
        assert_eq!(result, 5);
        Ok(())
    });
}

// FFI declaration
extern "C" {
    fn add_impl(a: usize, b: usize) -> usize;
}

fn call_lean_add(lean: Lean, a: usize, b: usize) -> LeanResult<usize> {
    unsafe {
        Ok(add_impl(a, b))
    }
}
```

## Current Status

⚠️ **These tests require Lean4 to be properly linked and will not run until:**
1. Lean4 is installed on the system
2. Build script successfully compiles Lean code
3. Linker can find Lean runtime and compiled Lean objects

## Future Work

- [ ] Implement build.rs to compile Lean code with Lake
- [ ] Add FFI declarations for exported Lean functions
- [ ] Test marshalling complex data types (arrays, strings, structures)
- [ ] Test error handling across the FFI boundary
- [ ] Test async/concurrent interactions
- [ ] Benchmark performance of FFI calls

## Examples

See `src/tests/` for example test cases demonstrating:
- Basic arithmetic operations
- String manipulation
- Array operations
- Complex data structures
- Error handling

## Troubleshooting

**Tests don't compile:**
- Check that Lean4 is installed: `lean --version`
- Check that Lake is available: `lake --version`
- Ensure LEAN_INCLUDE_DIR is set if Lean headers are in non-standard location

**Linker errors:**
- Verify that build.rs successfully compiled Lean code
- Check that Lean runtime library is accessible
- Try setting LD_LIBRARY_PATH (Linux) or DYLD_LIBRARY_PATH (macOS)

**Runtime errors:**
- Ensure `leo3::prepare_freethreaded_lean()` is called before tests
- Check that Lean function signatures match FFI declarations
- Verify data type conversions are correct
