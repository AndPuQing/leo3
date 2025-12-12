//! FFI bindings for Lean's Std.HashSet
//!
//! This module provides FFI declarations for Lean's HashSet functions.
//! These functions are exposed from the Lean runtime with the @[expose] attribute.

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

extern "C" {
    // ========================================================================
    // HashSet Creation
    // ========================================================================

    /// Create an empty HashSet with default capacity
    /// Signature: HashSet.empty [BEq α] [Hashable α] : HashSet α
    pub fn l_Std_HashSet_empty(beq: lean_obj_arg, hashable: lean_obj_arg) -> lean_obj_res;

    /// Create an empty HashSet with specified capacity
    /// Signature: HashSet.emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) : HashSet α
    pub fn l_Std_HashSet_emptyWithCapacity(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        capacity: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashSet Queries
    // ========================================================================

    /// Check if an element is present in the HashSet
    /// Signature: HashSet.contains (m : HashSet α) (a : α) : Bool
    pub fn l_Std_HashSet_contains(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: b_lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> u8;

    /// Get the size of the HashSet
    /// Signature: HashSet.size (m : HashSet α) : Nat
    pub fn l_Std_HashSet_size(m: b_lean_obj_arg) -> lean_obj_res;

    /// Check if the HashSet is empty
    /// Signature: HashSet.isEmpty (m : HashSet α) : Bool
    pub fn l_Std_HashSet_isEmpty(m: b_lean_obj_arg) -> u8;

    // ========================================================================
    // HashSet Modification
    // ========================================================================

    /// Insert an element into the HashSet (doesn't replace if exists)
    /// Signature: HashSet.insert (m : HashSet α) (a : α) : HashSet α
    pub fn l_Std_HashSet_insert(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
    ) -> lean_obj_res;

    /// Erase an element from the HashSet
    /// Signature: HashSet.erase (m : HashSet α) (a : α) : HashSet α
    pub fn l_Std_HashSet_erase(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if element exists, then insert (fused operation)
    /// Returns (Bool, HashSet) - true if element existed
    /// Signature: HashSet.containsThenInsert (m : HashSet α) (a : α) : Bool × HashSet α
    pub fn l_Std_HashSet_containsThenInsert(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
    ) -> lean_obj_res;

    /// Filter the HashSet by a predicate
    /// Signature: HashSet.filter (m : HashSet α) (p : α → Bool) : HashSet α
    pub fn l_Std_HashSet_filter(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        p: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashSet Set Operations
    // ========================================================================

    /// Test if all elements satisfy a predicate
    /// Signature: HashSet.all (m : HashSet α) (p : α → Bool) : Bool
    pub fn l_Std_HashSet_all(m: b_lean_obj_arg, p: lean_obj_arg) -> u8;

    /// Test if any element satisfies a predicate
    /// Signature: HashSet.any (m : HashSet α) (p : α → Bool) : Bool
    pub fn l_Std_HashSet_any(m: b_lean_obj_arg, p: lean_obj_arg) -> u8;

    // ========================================================================
    // HashSet Iteration
    // ========================================================================

    /// Fold over the HashSet
    /// Signature: HashSet.fold (f : σ → α → σ) (init : σ) (m : HashSet α) : σ
    pub fn l_Std_HashSet_fold(
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Monadic fold over the HashSet
    /// Signature: HashSet.foldM [Monad m] (f : σ → α → m σ) (init : σ) (m : HashSet α) : m σ
    pub fn l_Std_HashSet_foldM(
        monad: lean_obj_arg,
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// For-in loop over the HashSet
    /// Signature: HashSet.forIn [Monad m] (m : HashSet α) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ
    pub fn l_Std_HashSet_forIn(
        monad: lean_obj_arg,
        m: b_lean_obj_arg,
        init: lean_obj_arg,
        f: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashSet Conversion
    // ========================================================================

    /// Convert HashSet to List
    /// Signature: HashSet.toList (m : HashSet α) : List α
    pub fn l_Std_HashSet_toList(m: b_lean_obj_arg) -> lean_obj_res;

    /// Convert HashSet to Array
    /// Signature: HashSet.toArray (m : HashSet α) : Array α
    pub fn l_Std_HashSet_toArray(m: b_lean_obj_arg) -> lean_obj_res;

    /// Create HashSet from List
    /// Signature: HashSet.ofList [BEq α] [Hashable α] (l : List α) : HashSet α
    pub fn l_Std_HashSet_ofList(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        list: lean_obj_arg,
    ) -> lean_obj_res;

    /// Create HashSet from Array
    /// Signature: HashSet.ofArray [BEq α] [Hashable α] (a : Array α) : HashSet α
    pub fn l_Std_HashSet_ofArray(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        array: lean_obj_arg,
    ) -> lean_obj_res;
}
