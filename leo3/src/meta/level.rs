//! Universe levels for Lean's type theory
//!
//! Universe levels are used in sorts (Prop, Type u) to stratify types
//! and avoid paradoxes.

use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::LeanResult;
use leo3_ffi as ffi;

use super::name::LeanName;

/// Universe level
///
/// Levels form a hierarchy: 0 (Prop), 1 (Type), 2 (Type 1), ...
#[repr(transparent)]
pub struct LeanLevel {
    _private: (),
}

impl LeanLevel {
    /// Create level zero (Prop)
    ///
    /// # Example
    ///
    /// ```ignore
    /// let prop_level = LeanLevel::zero(lean)?;
    /// ```
    pub fn zero<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let ptr = ffi::expr::lean_level_mk_zero();
            if ptr.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_zero returned null - Lean.Expr may not be initialized correctly",
                ));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create level one (Type)
    ///
    /// This is implemented as succ(zero).
    ///
    /// # Example
    ///
    /// ```ignore
    /// let type_level = LeanLevel::one(lean)?;
    /// ```
    pub fn one<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let zero = ffi::expr::lean_level_mk_zero();
            if zero.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_zero returned null - Lean.Expr may not be initialized correctly",
                ));
            }
            let ptr = ffi::expr::lean_level_mk_succ(zero);
            if ptr.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_succ returned null - Lean.Expr may not be initialized correctly",
                ));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create successor level (level + 1)
    ///
    /// # Example
    ///
    /// ```ignore
    /// let level = LeanLevel::one(lean)?;
    /// let next_level = LeanLevel::succ(level)?; // Type 1
    /// ```
    pub fn succ<'l>(level: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let lean = level.lean_token();
            let ptr = ffi::expr::lean_level_mk_succ(level.into_ptr());
            if ptr.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_succ returned null",
                ));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create max of two levels
    ///
    /// # Example
    ///
    /// ```ignore
    /// let level = LeanLevel::max(a, b)?;
    /// ```
    pub fn max<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::expr::lean_level_mk_max(a.into_ptr(), b.into_ptr());
            if ptr.is_null() {
                return Err(crate::LeanError::runtime("lean_level_mk_max returned null"));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create imax of two levels
    ///
    /// imax is like max, but returns 0 if the second argument is 0.
    /// Used for dependent function types in Prop.
    pub fn imax<'l>(
        a: LeanBound<'l, Self>,
        b: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let lean = a.lean_token();
            let ptr = ffi::expr::lean_level_mk_imax(a.into_ptr(), b.into_ptr());
            if ptr.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_imax returned null",
                ));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a level parameter
    ///
    /// # Example
    ///
    /// ```ignore
    /// let u_name = LeanName::from_str(lean, "u")?;
    /// let param_level = LeanLevel::param(lean, u_name)?;
    /// ```
    pub fn param<'l>(
        lean: Lean<'l>,
        name: LeanBound<'l, LeanName>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_expr_initialized();
        unsafe {
            let ptr = ffi::expr::lean_level_mk_param(name.into_ptr());
            if ptr.is_null() {
                return Err(crate::LeanError::runtime(
                    "lean_level_mk_param returned null",
                ));
            }
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}
