# leo3-ffi-check

FFI validation tool for Leo3, ensuring our hand-written FFI bindings match Lean4's actual C API.

## Purpose

This crate is inspired by PyO3's `pyo3-ffi-check` and serves to:

1. **Validate struct layouts**: Ensures our `lean_object` and other structs match the actual sizes and alignments in Lean4's headers
2. **Check type aliases**: Verifies pointer types have correct sizes
3. **Prevent ABI breakage**: Catches mismatches that could cause crashes or undefined behavior
4. **Support multiple Lean versions**: Can validate against different Lean4 versions

## How It Works

1. **Build Script**: Uses `bindgen` to generate Rust bindings directly from `lean/lean.h`
2. **Layout Tests**: Compares sizes, alignments, and field offsets between our hand-written FFI and bindgen's output
3. **Validation**: Fails the build if any mismatches are detected

## Running

```bash
# Run FFI validation checks
cargo test -p leo3-ffi-check

# With specific Lean4 headers
LEAN_INCLUDE_DIR=/path/to/lean/include cargo test -p leo3-ffi-check
```

## Requirements

- **bindgen**: For generating bindings from C headers
- **Lean4 headers**: Must have `lean/lean.h` accessible
- **libclang**: Required by bindgen for parsing C headers

## Environment Variables

- `LEAN_INCLUDE_DIR`: Path to directory containing `lean/lean.h`
- If not set, checks common locations:
  - `/usr/local/include`
  - `/usr/include`
  - `/opt/homebrew/include`
  - `../lean4/src/include`

## What Gets Checked

### Structures
- [x] `lean_object` - Core Lean object struct
- [ ] Additional structs as we add them

### Type Aliases
- [x] `lean_obj_arg`
- [x] `b_lean_obj_arg`
- [x] `lean_obj_res`
- [x] `b_lean_obj_res`

### Constants
- [x] `LEAN_MAX_CTOR_TAG`
- [x] `LEAN_CLOSURE`
- [x] `LEAN_ARRAY`
- [x] `LEAN_STRING`
- [ ] Other tag constants

### Functions
- [x] Existence checks for core functions
- [ ] Signature validation (future work)

## Why This Matters

FFI bugs are hard to debug and can cause:
- **Segmentation faults**: From incorrect struct layouts
- **Memory corruption**: From wrong field offsets
- **Undefined behavior**: From ABI mismatches
- **Platform-specific issues**: That only appear on certain architectures

By validating against the actual headers, we catch these issues at compile time instead of runtime.

## Limitations

- **Function signatures**: Bindgen can generate function declarations, but validating calling conventions and ABI is complex
- **Preprocessor macros**: Some Lean macros may not be captured by bindgen
- **Inline functions**: Header-only inline functions need special handling

## Future Improvements

- [ ] Validate all structs from lean.h
- [ ] Check field offsets in addition to sizes
- [ ] Validate function pointer types
- [ ] Support for testing against multiple Lean4 versions in CI
- [x] Automated checks in GitHub Actions (gated in CI via `ffi-check` job)

## Related

- **leo3-ffi**: The actual FFI bindings this validates
- **leo3-build-config**: Detects Lean4 installation
- **PyO3's pyo3-ffi-check**: Inspiration for this approach
