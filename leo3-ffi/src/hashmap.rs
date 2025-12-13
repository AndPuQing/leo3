//! FFI bindings for Lean's Std.HashMap
//!
//! This module provides FFI declarations for Lean's HashMap functions.
//! These functions are exposed from the Lean runtime with the @\[expose\] attribute.

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

extern "C" {
    // ========================================================================
    // HashMap Creation
    // ========================================================================

    /// Create an empty HashMap with default capacity
    /// Signature: HashMap.empty [BEq α] [Hashable α] : HashMap α β
    pub fn l_Std_HashMap_empty(beq: lean_obj_arg, hashable: lean_obj_arg) -> lean_obj_res;

    /// Create an empty HashMap with specified capacity
    /// Signature: HashMap.emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) : HashMap α β
    pub fn l_Std_HashMap_emptyWithCapacity(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        capacity: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashMap Queries
    // ========================================================================

    /// Check if a key is present in the HashMap
    /// Signature: HashMap.contains (m : HashMap α β) (a : α) : Bool
    pub fn l_Std_HashMap_contains(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: b_lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> u8;

    /// Get the size of the HashMap
    /// Signature: HashMap.size (m : HashMap α β) : Nat
    pub fn l_Std_DHashMap_size(m: b_lean_obj_arg) -> lean_obj_res;

    /// Check if the HashMap is empty
    /// Signature: HashMap.isEmpty (m : HashMap α β) : Bool
    pub fn l_Std_DHashMap_isEmpty(m: b_lean_obj_arg) -> u8;

    // ========================================================================
    // HashMap Modification
    // ========================================================================

    /// Insert a key-value pair into the HashMap (replaces if exists)
    /// Signature: HashMap.insert (m : HashMap α β) (a : α) (b : β) : HashMap α β
    pub fn l_Std_DHashMap_insert(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        b: lean_obj_arg,
    ) -> lean_obj_res;

    /// Insert a key-value pair only if the key doesn't exist
    /// Signature: HashMap.insertIfNew (m : HashMap α β) (a : α) (b : β) : HashMap α β
    pub fn l_Std_DHashMap_insertIfNew(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        b: lean_obj_arg,
    ) -> lean_obj_res;

    /// Erase a key from the HashMap
    /// Signature: HashMap.erase (m : HashMap α β) (a : α) : HashMap α β
    pub fn l_Std_HashMap_erase(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if key exists, then insert (fused operation)
    /// Returns (Bool, HashMap) - true if key existed
    /// Signature: HashMap.containsThenInsert (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β
    pub fn l_Std_HashMap_containsThenInsert(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        b: lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if key exists, then insert only if new (fused operation)
    /// Returns (Bool, HashMap) - true if key existed
    /// Signature: HashMap.containsThenInsertIfNew (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β
    pub fn l_Std_HashMap_containsThenInsertIfNew(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        b: lean_obj_arg,
    ) -> lean_obj_res;

    /// Alter the value for a key with a function
    /// Signature: HashMap.alter (m : HashMap α β) (a : α) (f : Option β → Option β) : HashMap α β
    pub fn l_Std_HashMap_alter(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        f: lean_obj_arg,
    ) -> lean_obj_res;

    /// Filter the HashMap by a predicate
    /// Signature: HashMap.filter (m : HashMap α β) (p : α → β → Bool) : HashMap α β
    pub fn l_Std_HashMap_filter(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        m: lean_obj_arg,
        p: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashMap Iteration
    // ========================================================================

    /// Fold over the HashMap
    /// Signature: HashMap.fold (f : σ → α → β → σ) (init : σ) (m : HashMap α β) : σ
    pub fn l_Std_HashMap_fold(
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Monadic fold over the HashMap
    /// Signature: HashMap.foldM [Monad m] (f : σ → α → β → m σ) (init : σ) (m : HashMap α β) : m σ
    pub fn l_Std_HashMap_foldM(
        monad: lean_obj_arg,
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// For-in loop over the HashMap
    /// Signature: HashMap.forIn [Monad m] (m : HashMap α β) (init : σ) (f : α → β → σ → m (ForInStep σ)) : m σ
    pub fn l_Std_HashMap_forIn(
        monad: lean_obj_arg,
        m: b_lean_obj_arg,
        init: lean_obj_arg,
        f: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // HashMap Conversion
    // ========================================================================

    /// Convert HashMap to List
    /// Signature: HashMap.toList (m : HashMap α β) : List (α × β)
    pub fn l_Std_DHashMap_toList(m: b_lean_obj_arg) -> lean_obj_res;

    /// Convert HashMap to Array
    /// Signature: HashMap.toArray (m : HashMap α β) : Array (α × β)
    pub fn l_Std_DHashMap_toArray(m: b_lean_obj_arg) -> lean_obj_res;

    /// Create HashMap from List
    /// Signature: HashMap.ofList [BEq α] [Hashable α] (l : List (α × β)) : HashMap α β
    pub fn l_Std_HashMap_ofList(
        beq: lean_obj_arg,
        hashable: lean_obj_arg,
        list: lean_obj_arg,
    ) -> lean_obj_res;

    /// Get keys as an array
    /// Signature: HashMap.keysArray (m : HashMap α β) : Array α
    pub fn l_Std_DHashMap_keysArray(m: b_lean_obj_arg) -> lean_obj_res;

    /// Get values as an array
    /// Signature: HashMap.valuesArray (m : HashMap α β) : Array β
    pub fn l_Std_DHashMap_valuesArray(m: b_lean_obj_arg) -> lean_obj_res;
}
