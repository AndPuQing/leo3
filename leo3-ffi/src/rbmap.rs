//! FFI bindings for Lean's Lean.RBMap
//!
//! This module provides FFI declarations for Lean's RBMap (Red-Black Map) functions.
//! These functions are exposed from the Lean runtime with the @[expose] attribute.
//!
//! Note: RBMap uses Ord typeclass for comparison, not BEq/Hashable like HashMap.

use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res};

extern "C" {
    // ========================================================================
    // RBMap Creation
    // ========================================================================

    /// Create an empty RBMap
    /// Signature: RBMap.empty [Ord α] : RBMap α β
    pub fn l_Lean_RBMap_empty(ord: lean_obj_arg) -> lean_obj_res;

    // ========================================================================
    // RBMap Queries
    // ========================================================================

    /// Check if a key is present in the RBMap
    /// Signature: RBMap.contains (m : RBMap α β) (a : α) : Bool
    pub fn l_Lean_RBMap_contains(ord: lean_obj_arg, m: b_lean_obj_arg, a: b_lean_obj_arg) -> u8;

    /// Find a value by key (returns Option)
    /// Signature: RBMap.find? (m : RBMap α β) (a : α) : Option β
    pub fn l_Lean_RBMap_find_x3f(
        ord: lean_obj_arg,
        m: b_lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Find a value by key with default
    /// Signature: RBMap.findD (m : RBMap α β) (a : α) (default : β) : β
    pub fn l_Lean_RBMap_findD(
        ord: lean_obj_arg,
        m: b_lean_obj_arg,
        a: b_lean_obj_arg,
        default: lean_obj_arg,
    ) -> lean_obj_res;

    /// Find a value by key (panics if not found)
    /// Signature: RBMap.find! (m : RBMap α β) (a : α) [Inhabited β] : β
    pub fn l_Lean_RBMap_find_x21(
        inhabited: lean_obj_arg,
        ord: lean_obj_arg,
        m: b_lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Get the depth of the tree
    /// Signature: RBMap.depth (m : RBMap α β) : Nat
    pub fn l_Lean_RBMap_depth(m: b_lean_obj_arg) -> lean_obj_res;

    // ========================================================================
    // RBMap Modification
    // ========================================================================

    /// Insert a key-value pair into the RBMap
    /// Signature: RBMap.insert (m : RBMap α β) (a : α) (b : β) : RBMap α β
    pub fn l_Lean_RBMap_insert(
        ord: lean_obj_arg,
        m: lean_obj_arg,
        a: lean_obj_arg,
        b: lean_obj_arg,
    ) -> lean_obj_res;

    /// Erase a key from the RBMap
    /// Signature: RBMap.erase (m : RBMap α β) (a : α) : RBMap α β
    pub fn l_Lean_RBMap_erase(
        ord: lean_obj_arg,
        m: lean_obj_arg,
        a: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Filter the RBMap by a predicate
    /// Signature: RBMap.filter (m : RBMap α β) (p : α → β → Bool) : RBMap α β
    pub fn l_Lean_RBMap_filter(ord: lean_obj_arg, m: lean_obj_arg, p: lean_obj_arg)
        -> lean_obj_res;

    /// Filter and map the RBMap
    /// Signature: RBMap.filterMap (m : RBMap α β) (f : α → β → Option γ) : RBMap α γ
    pub fn l_Lean_RBMap_filterMap(
        ord: lean_obj_arg,
        m: lean_obj_arg,
        f: lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // RBMap Set Operations
    // ========================================================================

    /// Test if all key-value pairs satisfy a predicate
    /// Signature: RBMap.all (m : RBMap α β) (p : α → β → Bool) : Bool
    pub fn l_Lean_RBMap_all(m: b_lean_obj_arg, p: lean_obj_arg) -> u8;

    /// Test if any key-value pair satisfies a predicate
    /// Signature: RBMap.any (m : RBMap α β) (p : α → β → Bool) : Bool
    pub fn l_Lean_RBMap_any(m: b_lean_obj_arg, p: lean_obj_arg) -> u8;

    // ========================================================================
    // RBMap Iteration
    // ========================================================================

    /// Fold over the RBMap (in-order traversal)
    /// Signature: RBMap.fold (f : σ → α → β → σ) (init : σ) (m : RBMap α β) : σ
    pub fn l_Lean_RBMap_fold(
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// Monadic fold over the RBMap
    /// Signature: RBMap.foldM [Monad m] (f : σ → α → β → m σ) (init : σ) (m : RBMap α β) : m σ
    pub fn l_Lean_RBMap_foldM(
        monad: lean_obj_arg,
        f: lean_obj_arg,
        init: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    /// For-in loop over the RBMap
    /// Signature: RBMap.forIn [Monad m] (m : RBMap α β) (init : σ) (f : α → β → σ → m (ForInStep σ)) : m σ
    pub fn l_Lean_RBMap_forIn(
        monad: lean_obj_arg,
        m: b_lean_obj_arg,
        init: lean_obj_arg,
        f: lean_obj_arg,
    ) -> lean_obj_res;

    /// For-each monadic action over the RBMap
    /// Signature: RBMap.forM [Monad m] (f : α → β → m Unit) (m : RBMap α β) : m Unit
    pub fn l_Lean_RBMap_forM(
        monad: lean_obj_arg,
        f: lean_obj_arg,
        m: b_lean_obj_arg,
    ) -> lean_obj_res;

    // ========================================================================
    // RBMap Conversion
    // ========================================================================

    /// Create RBMap from Array
    /// Signature: RBMap.fromArray [Ord α] (a : Array (α × β)) : RBMap α β
    pub fn l_Lean_RBMap_fromArray(ord: lean_obj_arg, array: lean_obj_arg) -> lean_obj_res;

    /// Convert RBMap to List (in sorted order)
    /// Signature: RBMap.toList (m : RBMap α β) : List (α × β)
    pub fn l_Lean_RBMap_toList(m: b_lean_obj_arg) -> lean_obj_res;

    /// Convert RBMap to Array (in sorted order)
    /// Signature: RBMap.toArray (m : RBMap α β) : Array (α × β)
    pub fn l_Lean_RBMap_toArray(m: b_lean_obj_arg) -> lean_obj_res;
}
