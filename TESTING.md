# Leo3 Testing Infrastructure

This document outlines Leo3's testing approach, inspired by PyO3's comprehensive testing infrastructure.

## Current Test Organization

### Integration Tests (`leo3/tests/`)
- `basic.rs` - Runtime initialization and basic operations
- `string_ops.rs` - String creation, manipulation, and comparison
- `nat_ops.rs` - Natural number arithmetic and comparisons
- `array_ops.rs` - Array operations and manipulation
- `test_utils/` - Shared test utilities and macros

### Example Tests
- `examples/basic/` - Comprehensive usage example

## Test Utilities

### Available Macros
- `assert_lean_nat_eq!(a, b)` - Assert Lean nats are equal
- `assert_lean_string_eq!(a, b)` - Assert Lean strings are equal
- `assert_lean_nat_value!(nat, expected)` - Assert nat has expected value
- `assert_lean_string_value!(str, expected)` - Assert string has expected value
- `assert_lean_array_size!(arr, size)` - Assert array has expected size

### Helper Functions
- `with_lean_test(f)` - Run test with Lean runtime initialized and assert success

## Running Tests

### Run all tests (requires Lean4 linked):
```bash
cargo test --workspace
```

### Run specific test suites:
```bash
cargo test --test basic
cargo test --test string_ops
cargo test --test nat_ops
cargo test --test array_ops
```

### Run with specific features:
```bash
cargo test --features macros
cargo test --no-default-features
```

## Test Naming Conventions

Following PyO3's pattern:
- `test_<type>_<operation>.rs` - Tests for specific type operations
- `test_<feature>.rs` - Tests for specific features
- UI tests: `ui/<error_type>_<scenario>.rs`

## Contributing Tests

When adding new functionality:
1. Add unit tests in the implementation file
2. Add integration tests in `tests/`
3. Add examples demonstrating usage
4. Consider compile-time error tests for invalid usage
5. Update this roadmap as needed

## Key Differences from PyO3

- **No Python → Lean side testing yet**: PyO3 tests both Rust→Python and Python→Rust. Leo3 will need to test both Rust→Lean and Lean→Rust once that functionality is implemented.
- **Simpler feature matrix**: Lean4 has fewer variants than Python (no PyPy/GraalPy equivalent)
- **ABI stability**: Lean4's ABI is more stable than Python's, simplifying testing

## References

- PyO3 Testing Infrastructure: `/home/happy/work/pyo3/tests/`
- PyO3 FFI Checking: `/home/happy/work/pyo3/pyo3-ffi-check/`
- Lean4 Headers: `/home/happy/work/lean4/src/include/lean/`
