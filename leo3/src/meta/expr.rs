//! High-level wrapper for Lean expressions
//!
//! Expressions are the core term language of Lean, representing types, terms, and proofs.
//! This module provides the full expression API for constructing, inspecting, and transforming
//! Lean terms.

use crate::err::LeanError;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanList, LeanNat, LeanString};
use crate::LeanResult;
use leo3_ffi as ffi;

// TODO: Implement proper LeanName type wrapper
type LeanName = LeanString;

/// Lean expression - the core term language
///
/// Expressions represent:
/// - Types (Prop, Type u, function types)
/// - Terms (constants, applications, lambdas)
/// - Proofs
///
/// Expression kinds (12 variants):
/// - BVar: Bound variables (de Bruijn indices)
/// - FVar: Free variables
/// - MVar: Meta variables
/// - Sort: Universes (Prop, Type u)
/// - Const: Named constants
/// - App: Function application
/// - Lambda: λ abstractions
/// - Forall: ∀/Π types
/// - Let: Local definitions
/// - Lit: Literals (Nat, String)
/// - MData: Metadata wrapper
/// - Proj: Structure projections
#[repr(transparent)]
pub struct LeanExpr {
    _private: (),
}

impl LeanExpr {
    // ============ Constructors ============

    /// Create a bound variable (de Bruijn index)
    ///
    /// Bound variables reference binders (lambda, forall, let) using de Bruijn indices,
    /// where 0 is the most recent binder, 1 is the next outer, etc.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let var0 = LeanExpr::bvar(lean, 0)?;  // Most recent binding
    /// let var1 = LeanExpr::bvar(lean, 1)?;  // Next outer binding
    /// ```
    pub fn bvar<'l>(lean: Lean<'l>, idx: usize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let idx_nat = LeanNat::from_usize(lean, idx)?;
            let ptr = ffi::expr::lean_expr_mk_bvar(idx_nat.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a free variable
    ///
    /// Free variables have unique identifiers and are used in tactic state.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let fvar_id = LeanName::from_str(lean, "x.123")?;
    /// let fvar = LeanExpr::fvar(lean, fvar_id)?;
    /// ```
    pub fn fvar<'l>(
        lean: Lean<'l>,
        fvar_id: LeanBound<'l, LeanName>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::expr::lean_expr_mk_fvar(fvar_id.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a meta variable
    ///
    /// Meta variables represent holes to be filled during elaboration.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let mvar_id = LeanName::from_str(lean, "?m.1")?;
    /// let mvar = LeanExpr::mvar(lean, mvar_id)?;
    /// ```
    pub fn mvar<'l>(
        lean: Lean<'l>,
        mvar_id: LeanBound<'l, LeanName>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::expr::lean_expr_mk_mvar(mvar_id.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a sort (Prop or Type u)
    ///
    /// Sorts represent universes in Lean's type hierarchy.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let prop = LeanExpr::sort(lean, LeanLevel::zero(lean)?)?;  // Prop
    /// let type0 = LeanExpr::sort(lean, LeanLevel::one(lean)?)?;  // Type
    /// ```
    pub fn sort<'l>(
        lean: Lean<'l>,
        level: LeanBound<'l, super::level::LeanLevel>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::expr::lean_expr_mk_sort(level.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a constant reference
    ///
    /// Constants reference declarations in the environment by name.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name = LeanName::from_str(lean, "Nat.add")?;
    /// let levels = LeanList::nil(lean)?;
    /// let nat_add = LeanExpr::const_(lean, name, levels)?;
    /// ```
    pub fn const_<'l>(
        lean: Lean<'l>,
        name: LeanBound<'l, LeanName>,
        levels: LeanBound<'l, LeanList>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::expr::lean_expr_mk_const(name.into_ptr(), levels.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an application (f a)
    ///
    /// Applications represent function calls.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let f = LeanExpr::const_(/* ... */)?;
    /// let a = LeanExpr::bvar(lean, 0)?;
    /// let app = LeanExpr::app(&f, &a)?;
    /// ```
    pub fn app<'l>(
        fn_expr: &LeanBound<'l, Self>,
        arg_expr: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = fn_expr.lean_token();
            // Increment reference counts since the FFI will store these pointers
            ffi::lean_inc(fn_expr.as_ptr());
            ffi::lean_inc(arg_expr.as_ptr());
            let ptr = ffi::expr::lean_expr_mk_app(fn_expr.as_ptr(), arg_expr.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create multiple applications (f a b c)
    ///
    /// Convenience function for creating a chain of applications.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let add_3_5 = LeanExpr::mk_app(&nat_add, &[&three, &five])?;
    /// ```
    pub fn mk_app<'l>(
        fn_expr: &LeanBound<'l, Self>,
        args: &[&LeanBound<'l, Self>],
    ) -> LeanResult<LeanBound<'l, Self>> {
        let mut result = fn_expr.clone();
        for arg in args {
            result = Self::app(&result, arg)?;
        }
        Ok(result)
    }

    /// Create a lambda (λ x : type, body)
    ///
    /// Lambdas represent function abstractions.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let x_name = LeanName::from_str(lean, "x")?;
    /// let nat_type = /* ... */;
    /// let body = LeanExpr::bvar(lean, 0)?;  // Returns x
    /// let lambda = LeanExpr::lambda(x_name, nat_type, body, BinderInfo::Default)?;
    /// ```
    pub fn lambda<'l>(
        binder_name: LeanBound<'l, LeanName>,
        binder_type: LeanBound<'l, Self>,
        body: LeanBound<'l, Self>,
        binder_info: BinderInfo,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = binder_name.lean_token();
            let ptr = ffi::expr::lean_expr_mk_lambda(
                binder_name.into_ptr(),
                binder_type.into_ptr(),
                body.into_ptr(),
                binder_info.to_u8(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a forall/pi type (∀ x : type, body) or (type → body)
    ///
    /// Foralls represent dependent function types.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // ∀ (n : Nat), n + 0 = n
    /// let n_name = LeanName::from_str(lean, "n")?;
    /// let nat_type = /* ... */;
    /// let body = /* n + 0 = n */;
    /// let forall = LeanExpr::forall(n_name, nat_type, body, BinderInfo::Default)?;
    /// ```
    pub fn forall<'l>(
        binder_name: LeanBound<'l, LeanName>,
        binder_type: LeanBound<'l, Self>,
        body: LeanBound<'l, Self>,
        binder_info: BinderInfo,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = binder_name.lean_token();
            let ptr = ffi::expr::lean_expr_mk_forall(
                binder_name.into_ptr(),
                binder_type.into_ptr(),
                body.into_ptr(),
                binder_info.to_u8(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create an arrow type (A → B)
    ///
    /// Convenience function for non-dependent function types.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let nat_to_nat = LeanExpr::arrow(nat_type.clone(), nat_type)?;  // Nat → Nat
    /// ```
    pub fn arrow<'l>(
        domain: LeanBound<'l, Self>,
        codomain: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let lean = domain.lean_token();
        let dummy_name = LeanString::mk(lean, "_")?;
        Self::forall(dummy_name, domain, codomain, BinderInfo::Default)
    }

    /// Create a let expression (let x : type := value in body)
    ///
    /// Let expressions introduce local definitions.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // let x : Nat := 5 in x + x
    /// let x_name = LeanName::from_str(lean, "x")?;
    /// let nat_type = /* ... */;
    /// let five = /* ... */;
    /// let body = /* x + x */;
    /// let let_expr = LeanExpr::let_(x_name, nat_type, five, body, false)?;
    /// ```
    pub fn let_<'l>(
        decl_name: LeanBound<'l, LeanName>,
        type_: LeanBound<'l, Self>,
        value: LeanBound<'l, Self>,
        body: LeanBound<'l, Self>,
        non_dep: bool,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = decl_name.lean_token();
            let ptr = ffi::expr::lean_expr_mk_let(
                decl_name.into_ptr(),
                type_.into_ptr(),
                value.into_ptr(),
                body.into_ptr(),
                non_dep as u8,
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a literal expression
    ///
    /// # Example
    ///
    /// ```ignore
    /// let five_lit = LeanLiteral::nat(lean, 5)?;
    /// let five_expr = LeanExpr::lit(lean, five_lit)?;
    /// ```
    pub fn lit<'l>(
        lean: Lean<'l>,
        literal: LeanBound<'l, super::literal::LeanLiteral>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::expr::lean_expr_mk_lit(literal.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a metadata wrapper
    ///
    /// Metadata can attach additional information to expressions without affecting semantics.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let metadata = /* ... */;
    /// let expr = /* ... */;
    /// let mdata = LeanExpr::mdata(metadata, expr)?;
    /// ```
    pub fn mdata<'l>(
        metadata: LeanBound<'l, Self>,
        expr: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = metadata.lean_token();
            let ptr = ffi::expr::lean_expr_mk_mdata(metadata.into_ptr(), expr.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a projection (struct.field)
    ///
    /// Projections access fields of structures.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let struct_name = LeanName::from_str(lean, "Prod")?;
    /// let struct_expr = /* pair value */;
    /// let first = LeanExpr::proj(struct_name, 0, struct_expr)?;  // .fst
    /// ```
    pub fn proj<'l>(
        struct_name: LeanBound<'l, LeanName>,
        field_idx: usize,
        struct_expr: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = struct_name.lean_token();
            let idx_nat = LeanNat::from_usize(lean, field_idx)?;
            let ptr = ffi::expr::lean_expr_mk_proj(
                struct_name.into_ptr(),
                idx_nat.into_ptr(),
                struct_expr.into_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // ============ Pattern Matching ============

    /// Get expression kind
    ///
    /// Returns the variant tag of this expression.
    pub fn kind<'l>(expr: &LeanBound<'l, Self>) -> ExprKind {
        unsafe {
            let tag = ffi::lean_obj_tag(expr.as_ptr());
            ExprKind::from_u8(tag)
        }
    }

    /// Check if expression is a bound variable
    pub fn is_bvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::BVar
    }

    /// Check if expression is a free variable
    pub fn is_fvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::FVar
    }

    /// Check if expression is a meta variable
    pub fn is_mvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::MVar
    }

    /// Check if expression is a sort
    pub fn is_sort<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Sort
    }

    /// Check if expression is a constant
    pub fn is_const<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Const
    }

    /// Check if expression is an application
    pub fn is_app<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::App
    }

    /// Check if expression is a lambda
    pub fn is_lambda<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Lambda
    }

    /// Check if expression is a forall
    pub fn is_forall<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Forall
    }

    /// Check if expression is an arrow (non-dependent function type)
    ///
    /// Returns true if this is a forall where the bound variable doesn't occur in the body.
    pub fn is_arrow<'l>(expr: &LeanBound<'l, Self>) -> bool {
        if !Self::is_forall(expr) {
            return false;
        }
        if let Ok(body) = Self::forall_body(expr) {
            !Self::has_loose_bvar(&body, 0)
        } else {
            false
        }
    }

    /// Check if expression is a let
    pub fn is_let<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Let
    }

    /// Check if expression is a literal
    pub fn is_lit<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Lit
    }

    /// Check if expression is a metadata wrapper
    pub fn is_mdata<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::MData
    }

    /// Check if expression is a projection
    pub fn is_proj<'l>(expr: &LeanBound<'l, Self>) -> bool {
        Self::kind(expr) == ExprKind::Proj
    }

    // ============ Field Accessors ============

    /// Get bound variable index (requires: is_bvar)
    pub fn bvar_idx<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<usize> {
        if !Self::is_bvar(expr) {
            return Err(LeanError::runtime("Not a bound variable"));
        }
        unsafe {
            let lean = expr.lean_token();
            let idx_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0);
            let idx_nat = LeanBound::<LeanNat>::from_borrowed_ptr(lean, idx_ptr);
            LeanNat::to_usize(&idx_nat)
        }
    }

    /// Get free variable ID (requires: is_fvar)
    pub fn fvar_id<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_fvar(expr) {
            return Err(LeanError::runtime("Not a free variable"));
        }
        unsafe {
            let lean = expr.lean_token();
            let id_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(id_ptr);
            Ok(LeanBound::from_owned_ptr(lean, id_ptr))
        }
    }

    /// Get meta variable ID (requires: is_mvar)
    pub fn mvar_id<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_mvar(expr) {
            return Err(LeanError::runtime("Not a meta variable"));
        }
        unsafe {
            let lean = expr.lean_token();
            let id_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(id_ptr);
            Ok(LeanBound::from_owned_ptr(lean, id_ptr))
        }
    }

    /// Get sort level (requires: is_sort)
    pub fn sort_level<'l>(
        expr: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, super::level::LeanLevel>> {
        if !Self::is_sort(expr) {
            return Err(LeanError::runtime("Not a sort"));
        }
        unsafe {
            let lean = expr.lean_token();
            let level_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(level_ptr);
            Ok(LeanBound::from_owned_ptr(lean, level_ptr))
        }
    }

    /// Get constant name (requires: is_const)
    pub fn const_name<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_const(expr) {
            return Err(LeanError::runtime("Not a constant"));
        }
        unsafe {
            let lean = expr.lean_token();
            let name_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(name_ptr);
            Ok(LeanBound::from_owned_ptr(lean, name_ptr))
        }
    }

    /// Get constant levels (requires: is_const)
    pub fn const_levels<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanList>> {
        if !Self::is_const(expr) {
            return Err(LeanError::runtime("Not a constant"));
        }
        unsafe {
            let lean = expr.lean_token();
            let levels_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(levels_ptr);
            Ok(LeanBound::from_owned_ptr(lean, levels_ptr))
        }
    }

    /// Get application function (requires: is_app)
    pub fn app_fn<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_app(expr) {
            return Err(LeanError::runtime("Not an application"));
        }
        unsafe {
            let lean = expr.lean_token();
            let fn_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(fn_ptr);
            Ok(LeanBound::from_owned_ptr(lean, fn_ptr))
        }
    }

    /// Get application argument (requires: is_app)
    pub fn app_arg<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_app(expr) {
            return Err(LeanError::runtime("Not an application"));
        }
        unsafe {
            let lean = expr.lean_token();
            let arg_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(arg_ptr);
            Ok(LeanBound::from_owned_ptr(lean, arg_ptr))
        }
    }

    /// Get lambda binder name (requires: is_lambda)
    pub fn lambda_name<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_lambda(expr) {
            return Err(LeanError::runtime("Not a lambda"));
        }
        unsafe {
            let lean = expr.lean_token();
            let name_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(name_ptr);
            Ok(LeanBound::from_owned_ptr(lean, name_ptr))
        }
    }

    /// Get lambda binder type (requires: is_lambda)
    pub fn lambda_type<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_lambda(expr) {
            return Err(LeanError::runtime("Not a lambda"));
        }
        unsafe {
            let lean = expr.lean_token();
            let type_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(type_ptr);
            Ok(LeanBound::from_owned_ptr(lean, type_ptr))
        }
    }

    /// Get lambda body (requires: is_lambda)
    pub fn lambda_body<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_lambda(expr) {
            return Err(LeanError::runtime("Not a lambda"));
        }
        unsafe {
            let lean = expr.lean_token();
            let body_ptr = ffi::lean_ctor_get(expr.as_ptr(), 2) as *mut ffi::lean_object;
            ffi::lean_inc(body_ptr);
            Ok(LeanBound::from_owned_ptr(lean, body_ptr))
        }
    }

    /// Get lambda binder info (requires: is_lambda)
    pub fn lambda_info<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<BinderInfo> {
        if !Self::is_lambda(expr) {
            return Err(LeanError::runtime("Not a lambda"));
        }
        unsafe {
            let info_u8 = ffi::expr::lean_expr_binder_info(expr.as_ptr());
            Ok(BinderInfo::from_u8(info_u8))
        }
    }

    /// Get forall binder name (requires: is_forall)
    pub fn forall_name<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_forall(expr) {
            return Err(LeanError::runtime("Not a forall"));
        }
        unsafe {
            let lean = expr.lean_token();
            let name_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(name_ptr);
            Ok(LeanBound::from_owned_ptr(lean, name_ptr))
        }
    }

    /// Get forall domain type (requires: is_forall)
    pub fn forall_domain<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_forall(expr) {
            return Err(LeanError::runtime("Not a forall"));
        }
        unsafe {
            let lean = expr.lean_token();
            let domain_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(domain_ptr);
            Ok(LeanBound::from_owned_ptr(lean, domain_ptr))
        }
    }

    /// Get forall body (requires: is_forall)
    pub fn forall_body<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_forall(expr) {
            return Err(LeanError::runtime("Not a forall"));
        }
        unsafe {
            let lean = expr.lean_token();
            let body_ptr = ffi::lean_ctor_get(expr.as_ptr(), 2) as *mut ffi::lean_object;
            ffi::lean_inc(body_ptr);
            Ok(LeanBound::from_owned_ptr(lean, body_ptr))
        }
    }

    /// Get forall binder info (requires: is_forall)
    pub fn forall_info<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<BinderInfo> {
        if !Self::is_forall(expr) {
            return Err(LeanError::runtime("Not a forall"));
        }
        unsafe {
            let info_u8 = ffi::expr::lean_expr_binder_info(expr.as_ptr());
            Ok(BinderInfo::from_u8(info_u8))
        }
    }

    /// Get let declaration name (requires: is_let)
    pub fn let_name<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_let(expr) {
            return Err(LeanError::runtime("Not a let expression"));
        }
        unsafe {
            let lean = expr.lean_token();
            let name_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(name_ptr);
            Ok(LeanBound::from_owned_ptr(lean, name_ptr))
        }
    }

    /// Get let type (requires: is_let)
    pub fn let_type<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_let(expr) {
            return Err(LeanError::runtime("Not a let expression"));
        }
        unsafe {
            let lean = expr.lean_token();
            let type_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(type_ptr);
            Ok(LeanBound::from_owned_ptr(lean, type_ptr))
        }
    }

    /// Get let value (requires: is_let)
    pub fn let_value<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_let(expr) {
            return Err(LeanError::runtime("Not a let expression"));
        }
        unsafe {
            let lean = expr.lean_token();
            let value_ptr = ffi::lean_ctor_get(expr.as_ptr(), 2) as *mut ffi::lean_object;
            ffi::lean_inc(value_ptr);
            Ok(LeanBound::from_owned_ptr(lean, value_ptr))
        }
    }

    /// Get let body (requires: is_let)
    pub fn let_body<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_let(expr) {
            return Err(LeanError::runtime("Not a let expression"));
        }
        unsafe {
            let lean = expr.lean_token();
            let body_ptr = ffi::lean_ctor_get(expr.as_ptr(), 3) as *mut ffi::lean_object;
            ffi::lean_inc(body_ptr);
            Ok(LeanBound::from_owned_ptr(lean, body_ptr))
        }
    }

    /// Get projection struct name (requires: is_proj)
    pub fn proj_struct_name<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        if !Self::is_proj(expr) {
            return Err(LeanError::runtime("Not a projection"));
        }
        unsafe {
            let lean = expr.lean_token();
            let name_ptr = ffi::lean_ctor_get(expr.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(name_ptr);
            Ok(LeanBound::from_owned_ptr(lean, name_ptr))
        }
    }

    /// Get projection field index (requires: is_proj)
    pub fn proj_idx<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<usize> {
        if !Self::is_proj(expr) {
            return Err(LeanError::runtime("Not a projection"));
        }
        unsafe {
            let lean = expr.lean_token();
            let idx_ptr = ffi::lean_ctor_get(expr.as_ptr(), 1);
            let idx_nat = LeanBound::<LeanNat>::from_borrowed_ptr(lean, idx_ptr);
            LeanNat::to_usize(&idx_nat)
        }
    }

    /// Get projection struct expression (requires: is_proj)
    pub fn proj_struct<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        if !Self::is_proj(expr) {
            return Err(LeanError::runtime("Not a projection"));
        }
        unsafe {
            let lean = expr.lean_token();
            let struct_ptr = ffi::lean_ctor_get(expr.as_ptr(), 2) as *mut ffi::lean_object;
            ffi::lean_inc(struct_ptr);
            Ok(LeanBound::from_owned_ptr(lean, struct_ptr))
        }
    }

    // ============ Transformations ============

    /// Instantiate bound variables with expressions
    ///
    /// Replaces de Bruijn indices with expressions from the substitution array.
    /// Index 0 is replaced with subst[0], index 1 with subst[1], etc.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let lambda_body = /* ... has bvar 0 ... */;
    /// let subst_array = LeanArray::from_slice(lean, &[&some_value])?;
    /// let instantiated = LeanExpr::instantiate(&lambda_body, &subst_array)?;
    /// ```
    pub fn instantiate<'l>(
        expr: &LeanBound<'l, Self>,
        subst: &LeanBound<'l, crate::types::LeanArray>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_instantiate(expr.as_ptr(), subst.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Instantiate a single bound variable
    ///
    /// Replaces bvar 0 with the given value, and decrements all other indices.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let lambda_body = LeanExpr::bvar(lean, 0)?;
    /// let value = /* some expression */;
    /// let instantiated = LeanExpr::instantiate1(&lambda_body, &value)?;
    /// ```
    pub fn instantiate1<'l>(
        expr: &LeanBound<'l, Self>,
        value: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_instantiate1(expr.as_ptr(), value.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Instantiate bound variables in reverse order
    ///
    /// Similar to instantiate but processes substitutions in reverse.
    pub fn instantiate_rev<'l>(
        expr: &LeanBound<'l, Self>,
        subst: &LeanBound<'l, crate::types::LeanArray>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_instantiate_rev(expr.as_ptr(), subst.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Abstract free variables to bound variables
    ///
    /// Converts occurrences of free variables into de Bruijn indices.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let expr = /* contains fvars */;
    /// let fvars_array = LeanArray::from_slice(lean, &[&fvar1, &fvar2])?;
    /// let abstracted = LeanExpr::abstract_(&expr, &fvars_array)?;
    /// ```
    pub fn abstract_<'l>(
        expr: &LeanBound<'l, Self>,
        fvars: &LeanBound<'l, crate::types::LeanArray>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_abstract(expr.as_ptr(), fvars.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Abstract a range of free variables
    ///
    /// Similar to abstract but with an additional count parameter.
    pub fn abstract_range<'l>(
        expr: &LeanBound<'l, Self>,
        n: usize,
        fvars: &LeanBound<'l, crate::types::LeanArray>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let n_nat = LeanNat::from_usize(lean, n)?;
            let ptr = ffi::expr::lean_expr_abstract_range(
                expr.as_ptr(),
                n_nat.into_ptr(),
                fvars.as_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if expression has a loose bound variable at index
    ///
    /// Returns true if bvar with given index occurs free (not under enough binders).
    pub fn has_loose_bvar<'l>(expr: &LeanBound<'l, Self>, idx: usize) -> bool {
        unsafe {
            let lean = expr.lean_token();
            let idx_nat = match LeanNat::from_usize(lean, idx) {
                Ok(n) => n,
                Err(_) => return false,
            };
            ffi::expr::lean_expr_has_loose_bvar(expr.as_ptr(), idx_nat.as_ptr()) != 0
        }
    }

    /// Get the range of loose bound variables
    ///
    /// Returns the maximum de Bruijn index + 1, or 0 if no loose bvars.
    pub fn loose_bvar_range<'l>(expr: &LeanBound<'l, Self>) -> u32 {
        unsafe { ffi::expr::lean_expr_loose_bvar_range(expr.as_ptr()) }
    }

    /// Lift loose bound variables
    ///
    /// Increases de Bruijn indices >= start by delta.
    /// Used when moving expressions under additional binders.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Lift all variables by 1 (move under one more binder)
    /// let lifted = LeanExpr::lift_loose_bvars(&expr, 0, 1)?;
    /// ```
    pub fn lift_loose_bvars<'l>(
        expr: &LeanBound<'l, Self>,
        start: usize,
        delta: usize,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let start_nat = LeanNat::from_usize(lean, start)?;
            let delta_nat = LeanNat::from_usize(lean, delta)?;
            let ptr = ffi::expr::lean_expr_lift_loose_bvars(
                expr.as_ptr(),
                start_nat.into_ptr(),
                delta_nat.into_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Lower loose bound variables
    ///
    /// Decreases de Bruijn indices >= start by delta.
    /// Used when moving expressions from under binders.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Lower all variables by 1 (move out from under a binder)
    /// let lowered = LeanExpr::lower_loose_bvars(&expr, 0, 1)?;
    /// ```
    pub fn lower_loose_bvars<'l>(
        expr: &LeanBound<'l, Self>,
        start: usize,
        delta: usize,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let start_nat = LeanNat::from_usize(lean, start)?;
            let delta_nat = LeanNat::from_usize(lean, delta)?;
            let ptr = ffi::expr::lean_expr_lower_loose_bvars(
                expr.as_ptr(),
                start_nat.into_ptr(),
                delta_nat.into_ptr(),
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // ============ Comparison ============

    /// Alpha equivalence (ignores binder names)
    ///
    /// Returns true if expressions are equivalent up to renaming of bound variables.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // λ x, x  and  λ y, y  are alpha equivalent
    /// assert!(LeanExpr::alpha_eqv(&lambda_x, &lambda_y));
    /// ```
    pub fn alpha_eqv<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_eqv(a.as_ptr(), b.as_ptr()) != 0 }
    }

    /// Structural equality (includes binder names)
    ///
    /// Returns true if expressions are structurally identical.
    pub fn equal<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_equal(a.as_ptr(), b.as_ptr()) != 0 }
    }

    /// Quick structural ordering
    ///
    /// Fast comparison for sorting, may not be total order.
    pub fn quick_lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_quick_lt(a.as_ptr(), b.as_ptr()) != 0 }
    }

    /// Structural ordering
    ///
    /// Total order on expressions for use in maps/sets.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_lt(a.as_ptr(), b.as_ptr()) != 0 }
    }

    // ============ Utilities ============

    /// Get expression hash
    ///
    /// Returns a hash value for this expression.
    pub fn hash<'l>(expr: &LeanBound<'l, Self>) -> u64 {
        unsafe { ffi::expr::lean_expr_hash(expr.as_ptr()) }
    }

    /// Check if expression contains free variables
    pub fn has_fvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_has_fvar(expr.as_ptr()) != 0 }
    }

    /// Check if expression contains expression meta variables
    pub fn has_expr_mvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_has_expr_mvar(expr.as_ptr()) != 0 }
    }

    /// Check if expression contains level meta variables
    pub fn has_level_mvar<'l>(expr: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_has_level_mvar(expr.as_ptr()) != 0 }
    }

    /// Check if expression contains level parameters
    pub fn has_level_param<'l>(expr: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::expr::lean_expr_has_level_param(expr.as_ptr()) != 0 }
    }

    /// Get the debug string representation of an expression
    ///
    /// # Example
    ///
    /// ```ignore
    /// let expr = /* ... */;
    /// println!("Expression: {}", LeanExpr::dbg_to_string(&expr)?);
    /// ```
    pub fn dbg_to_string<'l>(expr: &LeanBound<'l, Self>) -> LeanResult<String> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_dbg_to_string(expr.as_ptr());
            let lean_str = LeanBound::<LeanString>::from_owned_ptr(lean, ptr);
            Ok(LeanString::cstr(&lean_str)?.to_string())
        }
    }

    /// Consume type annotations (optimization)
    ///
    /// Removes certain redundant type information for performance.
    pub fn consume_type_annotations<'l>(
        expr: LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = expr.lean_token();
            let ptr = ffi::expr::lean_expr_consume_type_annotations(expr.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }
}

/// Expression kind (12 variants)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExprKind {
    /// Bound variable (de Bruijn index)
    BVar,
    /// Free variable
    FVar,
    /// Meta variable
    MVar,
    /// Sort (Prop, Type u)
    Sort,
    /// Constant
    Const,
    /// Application
    App,
    /// Lambda abstraction
    Lambda,
    /// Forall/Pi type
    Forall,
    /// Let expression
    Let,
    /// Literal (Nat or String)
    Lit,
    /// Metadata wrapper
    MData,
    /// Projection
    Proj,
}

impl ExprKind {
    pub(crate) fn from_u8(val: u8) -> Self {
        match val {
            ffi::expr::LEAN_EXPR_BVAR => Self::BVar,
            ffi::expr::LEAN_EXPR_FVAR => Self::FVar,
            ffi::expr::LEAN_EXPR_MVAR => Self::MVar,
            ffi::expr::LEAN_EXPR_SORT => Self::Sort,
            ffi::expr::LEAN_EXPR_CONST => Self::Const,
            ffi::expr::LEAN_EXPR_APP => Self::App,
            ffi::expr::LEAN_EXPR_LAMBDA => Self::Lambda,
            ffi::expr::LEAN_EXPR_FORALL => Self::Forall,
            ffi::expr::LEAN_EXPR_LET => Self::Let,
            ffi::expr::LEAN_EXPR_LIT => Self::Lit,
            ffi::expr::LEAN_EXPR_MDATA => Self::MData,
            ffi::expr::LEAN_EXPR_PROJ => Self::Proj,
            _ => panic!("Invalid expression kind: {}", val),
        }
    }
}

/// Binder info for lambda and forall expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    /// Default (explicit argument)
    Default,
    /// Implicit argument
    Implicit,
    /// Strict implicit argument
    StrictImplicit,
    /// Instance implicit (type class)
    InstImplicit,
}

impl BinderInfo {
    pub(crate) fn from_u8(val: u8) -> Self {
        match val {
            ffi::expr::LEAN_BINDER_DEFAULT => Self::Default,
            ffi::expr::LEAN_BINDER_IMPLICIT => Self::Implicit,
            ffi::expr::LEAN_BINDER_STRICT_IMPLICIT => Self::StrictImplicit,
            ffi::expr::LEAN_BINDER_INST_IMPLICIT => Self::InstImplicit,
            _ => Self::Default,
        }
    }

    pub(crate) fn to_u8(self) -> u8 {
        match self {
            Self::Default => ffi::expr::LEAN_BINDER_DEFAULT,
            Self::Implicit => ffi::expr::LEAN_BINDER_IMPLICIT,
            Self::StrictImplicit => ffi::expr::LEAN_BINDER_STRICT_IMPLICIT,
            Self::InstImplicit => ffi::expr::LEAN_BINDER_INST_IMPLICIT,
        }
    }
}
