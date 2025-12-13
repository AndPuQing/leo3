//! FFI bindings for Lean's Expression API
//!
//! This module provides raw C FFI bindings for working with Lean expressions.
//! Expressions (Expr) are the core term language of Lean, representing types,
//! terms, and proofs.
//!
//! Based on:
//! - `/lean4/src/kernel/expr.cpp`
//! - `/lean4/src/Lean/Expr.lean`
//! - `/lean4/src/kernel/expr.h`

use super::*;

// ============================================================================
// Expression Tags (12 variants)
// ============================================================================

/// Expression kind: Bound variable (de Bruijn index)
pub const LEAN_EXPR_BVAR: u8 = 0;
/// Expression kind: Free variable
pub const LEAN_EXPR_FVAR: u8 = 1;
/// Expression kind: Meta variable
pub const LEAN_EXPR_MVAR: u8 = 2;
/// Expression kind: Sort (Prop, Type u)
pub const LEAN_EXPR_SORT: u8 = 3;
/// Expression kind: Constant
pub const LEAN_EXPR_CONST: u8 = 4;
/// Expression kind: Application
pub const LEAN_EXPR_APP: u8 = 5;
/// Expression kind: Lambda abstraction (λ)
pub const LEAN_EXPR_LAMBDA: u8 = 6;
/// Expression kind: Forall/Pi type (∀)
pub const LEAN_EXPR_FORALL: u8 = 7;
/// Expression kind: Let expression
pub const LEAN_EXPR_LET: u8 = 8;
/// Expression kind: Literal (Nat or String)
pub const LEAN_EXPR_LIT: u8 = 9;
/// Expression kind: Metadata wrapper
pub const LEAN_EXPR_MDATA: u8 = 10;
/// Expression kind: Projection (struct.field)
pub const LEAN_EXPR_PROJ: u8 = 11;

// ============================================================================
// Binder Info Constants
// ============================================================================

/// Binder info: Default (explicit argument)
pub const LEAN_BINDER_DEFAULT: u8 = 0;
/// Binder info: Implicit argument (inferred)
pub const LEAN_BINDER_IMPLICIT: u8 = 1;
/// Binder info: Strict implicit (must match exactly)
pub const LEAN_BINDER_STRICT_IMPLICIT: u8 = 2;
/// Binder info: Instance implicit (type class resolution)
pub const LEAN_BINDER_INST_IMPLICIT: u8 = 3;

// ============================================================================
// Expression Constructors
// ============================================================================

extern "C" {
    /// Create a bound variable expression
    ///
    /// Bound variables use de Bruijn indices:
    /// - 0 refers to the innermost binder
    /// - 1 refers to the next outer binder
    /// - etc.
    ///
    /// # Parameters
    /// - `idx`: Natural number representing the de Bruijn index (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.bvar idx)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.bvar : Nat → Expr
    /// ```
    pub fn lean_expr_mk_bvar(idx: lean_obj_arg) -> lean_obj_res;

    /// Create a free variable expression
    ///
    /// Free variables are named variables that appear in the local context.
    ///
    /// # Parameters
    /// - `fvar_id`: Name identifying the free variable (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.fvar fvar_id)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.fvar : FVarId → Expr
    /// ```
    pub fn lean_expr_mk_fvar(fvar_id: lean_obj_arg) -> lean_obj_res;

    /// Create a meta variable expression
    ///
    /// Meta variables are unification variables used during elaboration.
    ///
    /// # Parameters
    /// - `mvar_id`: Name identifying the meta variable (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.mvar mvar_id)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.mvar : MVarId → Expr
    /// ```
    pub fn lean_expr_mk_mvar(mvar_id: lean_obj_arg) -> lean_obj_res;

    /// Create a sort (universe) expression
    ///
    /// Sorts represent universes:
    /// - Prop (level zero)
    /// - Type u (level successor)
    ///
    /// # Parameters
    /// - `level`: Universe level (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.sort level)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.sort : Level → Expr
    /// ```
    pub fn lean_expr_mk_sort(level: lean_obj_arg) -> lean_obj_res;

    /// Create a constant expression
    ///
    /// Constants refer to named declarations in the environment.
    ///
    /// # Parameters
    /// - `name`: Name of the constant (consumed)
    /// - `levels`: List of universe level instantiations (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.const name levels)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.const : Name → List Level → Expr
    /// ```
    pub fn lean_expr_mk_const(name: lean_obj_arg, levels: lean_obj_arg) -> lean_obj_res;

    /// Create an application expression
    ///
    /// Applications represent function application: (f a)
    ///
    /// # Parameters
    /// - `fn_expr`: Function expression (borrowed)
    /// - `arg_expr`: Argument expression (borrowed)
    ///
    /// # Returns
    /// Expression object (Expr.app fn_expr arg_expr)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.app : Expr → Expr → Expr
    /// ```
    pub fn lean_expr_mk_app(fn_expr: lean_obj_arg, arg_expr: lean_obj_arg) -> lean_obj_res;

    /// Create a lambda abstraction
    ///
    /// Lambda expressions represent anonymous functions: λ (x : T), body
    ///
    /// # Parameters
    /// - `binder_name`: Name of the bound variable (consumed)
    /// - `binder_type`: Type of the bound variable (consumed)
    /// - `body`: Body expression (consumed)
    /// - `binder_info`: Binder info flags (LEAN_BINDER_*)
    ///
    /// # Returns
    /// Expression object (Expr.lam binder_name binder_type body binder_info)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.lam : Name → Expr → Expr → BinderInfo → Expr
    /// ```
    pub fn lean_expr_mk_lambda(
        binder_name: lean_obj_arg,
        binder_type: lean_obj_arg,
        body: lean_obj_arg,
        binder_info: u8,
    ) -> lean_obj_res;

    /// Create a forall/pi type
    ///
    /// Forall expressions represent dependent function types: ∀ (x : T), body
    /// Non-dependent functions (T → U) are represented as forall with unused variable.
    ///
    /// # Parameters
    /// - `binder_name`: Name of the bound variable (consumed)
    /// - `binder_type`: Type of the bound variable (domain) (consumed)
    /// - `body`: Body expression (codomain) (consumed)
    /// - `binder_info`: Binder info flags (LEAN_BINDER_*)
    ///
    /// # Returns
    /// Expression object (Expr.forallE binder_name binder_type body binder_info)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.forallE : Name → Expr → Expr → BinderInfo → Expr
    /// ```
    pub fn lean_expr_mk_forall(
        binder_name: lean_obj_arg,
        binder_type: lean_obj_arg,
        body: lean_obj_arg,
        binder_info: u8,
    ) -> lean_obj_res;

    /// Create a let expression
    ///
    /// Let expressions represent local definitions: let x : T := value in body
    ///
    /// # Parameters
    /// - `decl_name`: Name of the local definition (consumed)
    /// - `type_`: Type of the definition (consumed)
    /// - `value`: Value of the definition (consumed)
    /// - `body`: Body expression where the definition is in scope (consumed)
    /// - `non_dep`: 0 if dependent (x used in body), non-zero if non-dependent
    ///
    /// # Returns
    /// Expression object (Expr.letE decl_name type_ value body non_dep)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.letE : Name → Expr → Expr → Expr → Bool → Expr
    /// ```
    pub fn lean_expr_mk_let(
        decl_name: lean_obj_arg,
        type_: lean_obj_arg,
        value: lean_obj_arg,
        body: lean_obj_arg,
        non_dep: u8,
    ) -> lean_obj_res;

    /// Create a literal expression
    ///
    /// Literals represent primitive values (Nat or String literals).
    ///
    /// # Parameters
    /// - `literal`: Literal value object (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.lit literal)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.lit : Literal → Expr
    /// ```
    pub fn lean_expr_mk_lit(literal: lean_obj_arg) -> lean_obj_res;

    /// Create a metadata wrapper expression
    ///
    /// Metadata expressions attach metadata to expressions without changing their meaning.
    ///
    /// # Parameters
    /// - `metadata`: Metadata map (KVMap) (consumed)
    /// - `expr`: Expression to wrap (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.mdata metadata expr)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.mdata : MData → Expr → Expr
    /// ```
    pub fn lean_expr_mk_mdata(metadata: lean_obj_arg, expr: lean_obj_arg) -> lean_obj_res;

    /// Create a projection expression
    ///
    /// Projections represent structure field access: struct.field
    ///
    /// # Parameters
    /// - `struct_name`: Name of the structure type (consumed)
    /// - `field_idx`: Field index (Natural number) (consumed)
    /// - `struct_expr`: Expression of structure type (consumed)
    ///
    /// # Returns
    /// Expression object (Expr.proj struct_name field_idx struct_expr)
    ///
    /// # Lean type
    /// ```lean
    /// Expr.proj : Name → Nat → Expr → Expr
    /// ```
    pub fn lean_expr_mk_proj(
        struct_name: lean_obj_arg,
        field_idx: lean_obj_arg,
        struct_expr: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// Expression Inspection
// ============================================================================

extern "C" {
    /// Get the hash code of an expression
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// 64-bit hash code
    ///
    /// # Note
    /// Hash is cached in the expression's data field for efficiency
    pub fn lean_expr_hash(expr: lean_obj_arg) -> u64;

    /// Check if expression contains free variables
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// 0 if no free variables, non-zero if contains free variables
    pub fn lean_expr_has_fvar(expr: lean_obj_arg) -> u8;

    /// Check if expression contains expression meta variables
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// 0 if no expression mvars, non-zero if contains expression mvars
    pub fn lean_expr_has_expr_mvar(expr: lean_obj_arg) -> u8;

    /// Check if expression contains universe level meta variables
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// 0 if no level mvars, non-zero if contains level mvars
    pub fn lean_expr_has_level_mvar(expr: lean_obj_arg) -> u8;

    /// Check if expression contains universe level parameters
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// 0 if no level params, non-zero if contains level params
    pub fn lean_expr_has_level_param(expr: lean_obj_arg) -> u8;

    /// Get the range of loose bound variables
    ///
    /// Returns the smallest n such that all bound variables have index < n.
    /// If result is 0, the expression is closed (no loose bound variables).
    ///
    /// # Parameters
    /// - `expr`: Expression object (borrowed)
    ///
    /// # Returns
    /// Range as u32
    pub fn lean_expr_loose_bvar_range(expr: lean_obj_arg) -> u32;

    /// Get binder info from a binding expression (lambda or forall)
    ///
    /// # Parameters
    /// - `expr`: Expression object (must be lambda or forall) (borrowed)
    ///
    /// # Returns
    /// Binder info as u8 (LEAN_BINDER_*)
    ///
    /// # Safety
    /// Must only be called on lambda or forall expressions
    pub fn lean_expr_binder_info(expr: lean_obj_arg) -> u8;
}

// ============================================================================
// Expression Transformations
// ============================================================================

extern "C" {
    /// Instantiate bound variables with expressions
    ///
    /// Replaces de Bruijn indices with expressions from the substitution array.
    /// Variable n is replaced with subst\[n\].
    ///
    /// # Parameters
    /// - `expr`: Expression to instantiate (borrowed)
    /// - `subst`: Array of expressions for substitution (borrowed)
    ///
    /// # Returns
    /// New expression with variables substituted
    ///
    /// # Lean type
    /// ```lean
    /// Expr.instantiate : Expr → Array Expr → Expr
    /// ```
    pub fn lean_expr_instantiate(expr: lean_obj_arg, subst: lean_obj_arg) -> lean_obj_res;

    /// Instantiate a single bound variable
    ///
    /// Replaces variable 0 with the given expression.
    /// This is more efficient than instantiate for single substitutions.
    ///
    /// # Parameters
    /// - `expr`: Expression to instantiate (borrowed)
    /// - `value`: Expression to substitute for variable 0 (borrowed)
    ///
    /// # Returns
    /// New expression with variable 0 replaced
    ///
    /// # Lean type
    /// ```lean
    /// Expr.instantiate1 : Expr → Expr → Expr
    /// ```
    pub fn lean_expr_instantiate1(expr: lean_obj_arg, value: lean_obj_arg) -> lean_obj_res;

    /// Instantiate bound variables in reverse order
    ///
    /// Replaces variable n with subst[size-1-n].
    /// This is useful when building lambda/forall with multiple binders.
    ///
    /// # Parameters
    /// - `expr`: Expression to instantiate (borrowed)
    /// - `subst`: Array of expressions for substitution (borrowed)
    ///
    /// # Returns
    /// New expression with variables substituted in reverse
    ///
    /// # Lean type
    /// ```lean
    /// Expr.instantiateRev : Expr → Array Expr → Expr
    /// ```
    pub fn lean_expr_instantiate_rev(expr: lean_obj_arg, subst: lean_obj_arg) -> lean_obj_res;

    /// Instantiate a range of bound variables
    ///
    /// Replaces variables in range [begin, end) with expressions from subst.
    ///
    /// # Parameters
    /// - `expr`: Expression to instantiate (borrowed)
    /// - `begin`: Start of range (Natural number) (borrowed)
    /// - `end`: End of range (Natural number) (borrowed)
    /// - `subst`: Array of expressions for substitution (borrowed)
    ///
    /// # Returns
    /// New expression with range substituted
    pub fn lean_expr_instantiate_range(
        expr: lean_obj_arg,
        begin: lean_obj_arg,
        end: lean_obj_arg,
        subst: lean_obj_arg,
    ) -> lean_obj_res;

    /// Instantiate a range in reverse order
    ///
    /// # Parameters
    /// - `expr`: Expression to instantiate (borrowed)
    /// - `begin`: Start of range (Natural number) (borrowed)
    /// - `end`: End of range (Natural number) (borrowed)
    /// - `subst`: Array of expressions for substitution (borrowed)
    ///
    /// # Returns
    /// New expression with range substituted in reverse
    pub fn lean_expr_instantiate_rev_range(
        expr: lean_obj_arg,
        begin: lean_obj_arg,
        end: lean_obj_arg,
        subst: lean_obj_arg,
    ) -> lean_obj_res;

    /// Abstract free variables to bound variables
    ///
    /// Replaces occurrences of free variables with de Bruijn indices.
    /// fvar subst\[i\] is replaced with variable i.
    ///
    /// # Parameters
    /// - `expr`: Expression to abstract (borrowed)
    /// - `subst`: Array of free variable expressions (borrowed)
    ///
    /// # Returns
    /// New expression with fvars converted to bound variables
    ///
    /// # Lean type
    /// ```lean
    /// Expr.abstract : Expr → Array Expr → Expr
    /// ```
    pub fn lean_expr_abstract(expr: lean_obj_arg, subst: lean_obj_arg) -> lean_obj_res;

    /// Abstract a range of free variables
    ///
    /// # Parameters
    /// - `expr`: Expression to abstract (borrowed)
    /// - `n`: Number of variables to abstract (Natural number) (borrowed)
    /// - `subst`: Array of free variable expressions (borrowed)
    ///
    /// # Returns
    /// New expression with fvars abstracted
    pub fn lean_expr_abstract_range(
        expr: lean_obj_arg,
        n: lean_obj_arg,
        subst: lean_obj_arg,
    ) -> lean_obj_res;

    /// Check if expression has a loose bound variable at index
    ///
    /// # Parameters
    /// - `expr`: Expression to check (borrowed)
    /// - `idx`: Variable index (Natural number) (borrowed)
    ///
    /// # Returns
    /// 0 if variable at idx is not loose, non-zero if it is loose
    pub fn lean_expr_has_loose_bvar(expr: lean_obj_arg, idx: lean_obj_arg) -> u8;

    /// Lift loose bound variables
    ///
    /// Increases de Bruijn indices >= start by delta.
    /// Used when inserting new binders above existing variables.
    ///
    /// # Parameters
    /// - `expr`: Expression to transform (borrowed)
    /// - `start`: Starting index (Natural number) (borrowed)
    /// - `delta`: Amount to lift (Natural number) (borrowed)
    ///
    /// # Returns
    /// New expression with variables lifted
    ///
    /// # Lean type
    /// ```lean
    /// Expr.liftLooseBVars : Expr → Nat → Nat → Expr
    /// ```
    pub fn lean_expr_lift_loose_bvars(
        expr: lean_obj_arg,
        start: lean_obj_arg,
        delta: lean_obj_arg,
    ) -> lean_obj_res;

    /// Lower loose bound variables
    ///
    /// Decreases de Bruijn indices >= start by delta.
    /// Used when removing binders.
    ///
    /// # Parameters
    /// - `expr`: Expression to transform (borrowed)
    /// - `start`: Starting index (Natural number) (borrowed)
    /// - `delta`: Amount to lower (Natural number) (borrowed)
    ///
    /// # Returns
    /// New expression with variables lowered
    ///
    /// # Lean type
    /// ```lean
    /// Expr.lowerLooseBVars : Expr → Nat → Nat → Expr
    /// ```
    pub fn lean_expr_lower_loose_bvars(
        expr: lean_obj_arg,
        start: lean_obj_arg,
        delta: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// Expression Comparison
// ============================================================================

extern "C" {
    /// Check alpha equivalence
    ///
    /// Two expressions are alpha equivalent if they are structurally equal
    /// modulo renaming of bound variables. Binder names are ignored.
    ///
    /// # Parameters
    /// - `a`: First expression (borrowed)
    /// - `b`: Second expression (borrowed)
    ///
    /// # Returns
    /// 0 if not alpha equivalent, non-zero if alpha equivalent
    ///
    /// # Example
    /// ```text
    /// λ x, x  ≡ λ y, y  (alpha equivalent)
    /// λ x, x  ≢ λ x, 0  (not alpha equivalent)
    /// ```
    pub fn lean_expr_eqv(a: lean_obj_arg, b: lean_obj_arg) -> u8;

    /// Check structural equality
    ///
    /// Stricter than alpha equivalence - also compares binder names.
    ///
    /// # Parameters
    /// - `a`: First expression (borrowed)
    /// - `b`: Second expression (borrowed)
    ///
    /// # Returns
    /// 0 if not equal, non-zero if equal
    pub fn lean_expr_equal(a: lean_obj_arg, b: lean_obj_arg) -> u8;

    /// Quick ordering using hash codes
    ///
    /// Fast but approximate ordering based on hash codes.
    /// Used for quick sorting and filtering.
    ///
    /// # Parameters
    /// - `a`: First expression (borrowed)
    /// - `b`: Second expression (borrowed)
    ///
    /// # Returns
    /// 0 if a >= b, non-zero if a < b
    pub fn lean_expr_quick_lt(a: lean_obj_arg, b: lean_obj_arg) -> u8;

    /// Structural ordering
    ///
    /// Total order on expressions for use in maps and sets.
    ///
    /// # Parameters
    /// - `a`: First expression (borrowed)
    /// - `b`: Second expression (borrowed)
    ///
    /// # Returns
    /// 0 if a >= b, non-zero if a < b
    pub fn lean_expr_lt(a: lean_obj_arg, b: lean_obj_arg) -> u8;
}

// ============================================================================
// Debug and Utility
// ============================================================================

extern "C" {
    /// Convert expression to debug string representation
    ///
    /// Produces a string representation of the expression structure for debugging.
    /// Does not require an environment.
    ///
    /// # Parameters
    /// - `expr`: Expression to convert (borrowed)
    ///
    /// # Returns
    /// Lean String object containing debug representation
    ///
    /// # Note
    /// This is for debugging only. For proper pretty-printing, use the
    /// delaborator and formatter (requires environment context).
    pub fn lean_expr_dbg_to_string(expr: lean_obj_arg) -> lean_obj_res;

    /// Consume type annotations
    ///
    /// Removes metadata and other annotations for optimization.
    ///
    /// # Parameters
    /// - `expr`: Expression to clean (consumed)
    ///
    /// # Returns
    /// Expression with annotations removed
    pub fn lean_expr_consume_type_annotations(expr: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Literal Construction and Inspection
// ============================================================================

extern "C" {
    /// Get the type of a literal
    ///
    /// Returns the Expr representing the type of the literal.
    ///
    /// # Parameters
    /// - `lit`: Literal object (borrowed)
    ///
    /// # Returns
    /// Expression representing the literal's type (Nat or String)
    pub fn lean_lit_type(lit: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Universe Level Operations (subset)
// ============================================================================

extern "C" {
    /// Create level zero (Prop)
    ///
    /// # Returns
    /// Level object representing level zero
    pub fn lean_level_mk_zero() -> lean_obj_res;

    /// Create successor level
    ///
    /// # Parameters
    /// - `level`: Level to increment (consumed)
    ///
    /// # Returns
    /// Level object representing succ(level)
    pub fn lean_level_mk_succ(level: lean_obj_arg) -> lean_obj_res;

    /// Create max of two levels
    ///
    /// # Parameters
    /// - `a`: First level (consumed)
    /// - `b`: Second level (consumed)
    ///
    /// # Returns
    /// Level object representing max(a, b)
    pub fn lean_level_mk_max(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Create imax of two levels
    ///
    /// imax is like max, but returns 0 if the second argument is 0.
    /// Used for dependent function types in Prop.
    ///
    /// # Parameters
    /// - `a`: First level (consumed)
    /// - `b`: Second level (consumed)
    ///
    /// # Returns
    /// Level object representing imax(a, b)
    pub fn lean_level_mk_imax(a: lean_obj_arg, b: lean_obj_arg) -> lean_obj_res;

    /// Create a level parameter
    ///
    /// # Parameters
    /// - `name`: Parameter name (consumed)
    ///
    /// # Returns
    /// Level object representing parameter(name)
    pub fn lean_level_mk_param(name: lean_obj_arg) -> lean_obj_res;
}
