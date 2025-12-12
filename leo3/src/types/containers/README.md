# Container Types Implementation Status

## Current Status

The container types (HashMap, HashSet, RBMap) in `leo3/src/types/containers/` currently have **placeholder implementations**. These types compile and provide a type-safe API, but do not implement the actual Lean container behavior.

## FFI Bindings

We have created FFI bindings for Lean's container functions in `leo3-ffi/src/`:
- `hashmap.rs` - Std.HashMap FFI declarations
- `hashset.rs` - Std.HashSet FFI declarations
- `rbmap.rs` - Lean.RBMap FFI declarations

These bindings declare the functions available in Lean's shared library (e.g., `l_Std_HashMap_insert`, `l_Std_HashSet_contains`, etc.).

## The Challenge: Typeclass Instances

Using these FFI functions requires passing Lean typeclass instances:
- `HashMap` requires `BEq α` and `Hashable α` instances
- `HashSet` requires `BEq α` and `Hashable α` instances
- `RBMap` requires `Ord α` instance

These instances are Lean objects that must be obtained at runtime. There are several approaches to solve this:

### Approach 1: Lean-side Wrappers (Recommended)

Create Lean functions that bundle typeclass instances with operations:

```lean
-- In Lean:
@[export my_hashmap_nat_string_empty]
def myHashMapNatStringEmpty : HashMap Nat String :=
  HashMap.empty

@[export my_hashmap_nat_string_insert]
def myHashMapNatStringInsert (m : HashMap Nat String) (k : Nat) (v : String) : HashMap Nat String :=
  m.insert k v
```

Then call these from Rust:
```rust
extern "C" {
    fn my_hashmap_nat_string_empty() -> lean_obj_res;
    fn my_hashmap_nat_string_insert(m: lean_obj_arg, k: lean_obj_arg, v: lean_obj_arg) -> lean_obj_res;
}
```

### Approach 2: Eval-based Approach

Use Lean's evaluation system to execute Lean code directly:
```rust
// Pseudo-code:
let map = lean_eval("HashMap.empty : HashMap Nat String")?;
let map = lean_eval(&format!("({:?}).insert {} {}", map, key, value))?;
```

### Approach 3: Typeclass Instance Registry

Create a registry system that caches typeclass instances for common types:
```rust
pub struct TypeclassInstances {
    beq_nat: LeanBound<'static, BEqType<LeanNat>>,
    hashable_nat: LeanBound<'static, HashableType<LeanNat>>,
    // ... etc
}
```

## Recommended Next Steps

1. **For specific use cases**: Use Approach 1 - create Lean wrappers for the exact container types you need

2. **For general library support**: Implement Approach 3 - create a typeclass instance registry for common types

3. **Current implementation**: The placeholder implementations are sufficient for initial API design and testing. They should be clearly documented as placeholders.

## Available FFI Functions

All functions from the Lean standard library are available through the FFI bindings:

### HashMap
- `l_Std_HashMap_empty` / `l_Std_HashMap_emptyWithCapacity`
- `l_Std_DHashMap_insert` / `l_Std_DHashMap_insertIfNew`
- `l_Std_HashMap_contains`
- `l_Std_HashMap_erase`
- `l_Std_HashMap_alter`
- `l_Std_HashMap_filter`
- `l_Std_HashMap_fold` / `l_Std_HashMap_foldM`
- `l_Std_DHashMap_toList` / `l_Std_DHashMap_toArray`
- ... (see `leo3-ffi/src/hashmap.rs` for full list)

### HashSet
- `l_Std_HashSet_empty` / `l_Std_HashSet_emptyWithCapacity`
- `l_Std_HashSet_insert`
- `l_Std_HashSet_contains`
- `l_Std_HashSet_erase`
- `l_Std_HashSet_filter`
- `l_Std_HashSet_all` / `l_Std_HashSet_any`
- `l_Std_HashSet_fold` / `l_Std_HashSet_foldM`
- `l_Std_HashSet_toList` / `l_Std_HashSet_toArray`
- ... (see `leo3-ffi/src/hashset.rs` for full list)

### RBMap
- `l_Lean_RBMap_empty`
- `l_Lean_RBMap_insert`
- `l_Lean_RBMap_find_x3f` (`find?`) / `l_Lean_RBMap_findD`
- `l_Lean_RBMap_contains`
- `l_Lean_RBMap_erase`
- `l_Lean_RBMap_filter` / `l_Lean_RBMap_filterMap`
- `l_Lean_RBMap_fold` / `l_Lean_RBMap_foldM`
- `l_Lean_RBMap_toList` / `l_Lean_RBMap_toArray`
- ... (see `leo3-ffi/src/rbmap.rs` for full list)

## Function Name Consistency

All FFI function names match the Lean reference manual:
- Lean: `HashMap.insert` → FFI: `l_Std_HashMap_insert` (but uses DHashMap internally)
- Lean: `HashSet.contains` → FFI: `l_Std_HashSet_contains`
- Lean: `RBMap.find?` → FFI: `l_Lean_RBMap_find_x3f` (? encoded as _x3f)
- Lean: `RBMap.find!` → FFI: `l_Lean_RBMap_find_x21` (! encoded as _x21)

The naming convention is: `l_` + namespace path with underscores, and special characters encoded in hex.
