//! Literal values for Lean expressions
//!
//! Literals represent primitive values like natural numbers and strings.

use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanNat, LeanString};
use crate::LeanResult;
use leo3_ffi as ffi;

/// Literal value (Nat or String)
///
/// Literals can be embedded in expressions using `LeanExpr::lit`.
#[repr(transparent)]
pub struct LeanLiteral {
    _private: (),
}

impl LeanLiteral {
    /// Create a natural number literal
    ///
    /// Constructs a `Literal.natVal` value.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let five_lit = LeanLiteral::nat(lean, 5)?;
    /// let expr = LeanExpr::lit(lean, five_lit)?;
    /// ```
    pub fn nat<'l>(lean: Lean<'l>, val: u64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Literal.natVal has tag 0, 1 object field (the Nat), no scalar fields
            let nat_val = LeanNat::from_usize(lean, val as usize)?;
            let ptr = ffi::lean_alloc_ctor(0, 1, 0);
            ffi::lean_ctor_set(ptr, 0, nat_val.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a string literal
    ///
    /// Constructs a `Literal.strVal` value.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let hello_lit = LeanLiteral::string(lean, "Hello, World!")?;
    /// let expr = LeanExpr::lit(lean, hello_lit)?;
    /// ```
    pub fn string<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Literal.strVal has tag 1, 1 object field (the String), no scalar fields
            let string_val = LeanString::mk(lean, s)?;
            let ptr = ffi::lean_alloc_ctor(1, 1, 0);
            ffi::lean_ctor_set(ptr, 0, string_val.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the type of a literal
    ///
    /// Returns the expression representing the type (Nat or String).
    pub fn type_<'l>(
        lit: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, super::expr::LeanExpr>> {
        unsafe {
            let lean = lit.lean_token();
            let ptr = ffi::expr::lean_lit_type(lit.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}
