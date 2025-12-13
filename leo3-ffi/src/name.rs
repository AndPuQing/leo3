//! FFI bindings for Lean's Name API
//!
//! Names in Lean are hierarchical identifiers used for constants, variables, etc.
//! They are represented as an inductive type:
//! - `Name.anonymous`: The root/empty name
//! - `Name.str p s`: Append a string component to name `p`
//! - `Name.num p n`: Append a numeric component to name `p`
//!
//! Example: The name `Lean.Meta.run` is represented as:
//! ```lean
//! Name.str (Name.str (Name.str Name.anonymous "Lean") "Meta") "run"
//! ```
//!
//! Based on:
//! - `/lean4/src/Init/Prelude.lean` (Name definition)

use super::*;

// ============================================================================
// Name Tags
// ============================================================================

/// Name kind: Anonymous (root name)
pub const LEAN_NAME_ANONYMOUS: u8 = 0;
/// Name kind: String component
pub const LEAN_NAME_STR: u8 = 1;
/// Name kind: Numeric component
pub const LEAN_NAME_NUM: u8 = 2;

// ============================================================================
// Name Constructors
// ============================================================================

extern "C" {
    /// Create a name by appending a string component
    ///
    /// # Parameters
    /// - `pre`: Parent name (consumed)
    /// - `s`: String component (consumed)
    ///
    /// # Returns
    /// Name object (Name.str pre s)
    ///
    /// # Lean type
    /// ```lean
    /// Name.mkStr : Name → String → Name
    /// ```
    pub fn lean_name_mk_string(pre: lean_obj_arg, s: lean_obj_arg) -> lean_obj_res;

    /// Create a name by appending a numeric component
    ///
    /// # Parameters
    /// - `pre`: Parent name (consumed)
    /// - `n`: Numeric value (consumed)
    ///
    /// # Returns
    /// Name object (Name.num pre n)
    ///
    /// # Lean type
    /// ```lean
    /// Name.mkNum : Name → Nat → Name
    /// ```
    pub fn lean_name_mk_numeral(pre: lean_obj_arg, n: lean_obj_arg) -> lean_obj_res;

    /// Compare two names for equality
    ///
    /// # Parameters
    /// - `a`: First name (borrowed)
    /// - `b`: Second name (borrowed)
    ///
    /// # Returns
    /// 0 if not equal, non-zero if equal
    pub fn lean_name_eq(a: b_lean_obj_arg, b: b_lean_obj_arg) -> u8;
}
