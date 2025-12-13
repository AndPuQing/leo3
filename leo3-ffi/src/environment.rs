//! FFI bindings for Lean's Environment API
//!
//! This module provides raw C FFI bindings for working with Lean environments.
//! Environments are the core of Lean's module system, storing declarations, constants,
//! inductive types, and type class instances.
//!
//! Based on:
//! - `/lean4/src/kernel/environment.cpp`
//! - `/lean4/src/Lean/Environment.lean`
//! - `/lean4/src/kernel/declaration.cpp`

use super::*;

// ============================================================================
// Environment Creation and Management
// ============================================================================

extern "C" {
    /// Create an empty environment with the specified trust level
    ///
    /// Trust level controls type checking:
    /// - 0: Full type checking (safest)
    /// - Higher values: Skip certain type checking operations (faster, less safe)
    ///
    /// Returns: `IO Environment` (requires IO execution to extract the environment)
    ///
    /// # Safety
    /// Must be called after lean runtime initialization
    pub fn lean_mk_empty_environment(trust_level: u32) -> lean_obj_res;
}

// ============================================================================
// Environment Queries
// ============================================================================

extern "C" {
    /// Find a constant by name in the environment
    ///
    /// # Parameters
    /// - `env`: Environment object (borrowed)
    /// - `name`: Name object (borrowed)
    ///
    /// # Returns
    /// `Option ConstantInfo` - Some if constant exists, None otherwise
    ///
    /// # Example (C++)
    /// ```cpp
    /// optional<constant_info> environment::find(name const & n) const;
    /// ```
    pub fn lean_environment_find(env: lean_obj_arg, name: lean_obj_arg) -> lean_obj_res;

    /// Check if the Quot type has been initialized in the environment
    ///
    /// # Returns
    /// 0 if not initialized, non-zero if initialized
    pub fn lean_environment_quot_init(env: lean_obj_arg) -> u8;
}

// ============================================================================
// Environment Modifications (Immutable Updates)
// ============================================================================

extern "C" {
    /// Add a declaration to the environment with type checking
    ///
    /// This performs full type checking on the declaration before adding it.
    /// The environment is immutable, so this returns a new environment.
    ///
    /// # Parameters
    /// - `env`: Environment object (consumed)
    /// - `max_heartbeat`: Maximum heartbeats for type checking (0 = unlimited)
    /// - `decl`: Declaration object (borrowed)
    /// - `cancel_token`: Optional IO.CancelToken for cancellation (can be null)
    ///
    /// # Returns
    /// `Except Kernel.Exception Environment` - Ok with new environment or Error with exception
    ///
    /// # Lean signature
    /// ```lean
    /// lean_add_decl : Environment → USize → Declaration → Option CancelToken → Except Exception Environment
    /// ```
    pub fn lean_add_decl(
        env: lean_obj_arg,
        max_heartbeat: usize,
        decl: lean_obj_arg,
        cancel_token: lean_obj_arg,
    ) -> lean_obj_res;

    /// Add a declaration to the environment without type checking
    ///
    /// **Warning**: This skips type checking entirely. Only use if you're certain
    /// the declaration is well-typed. Much faster than `lean_add_decl` but unsafe.
    ///
    /// # Parameters
    /// - `env`: Environment object (consumed)
    /// - `decl`: Declaration object (borrowed)
    ///
    /// # Returns
    /// `Except Kernel.Exception Environment`
    ///
    /// # Lean signature
    /// ```lean
    /// lean_add_decl_without_checking : Environment → Declaration → Except Exception Environment
    /// ```
    pub fn lean_add_decl_without_checking(env: lean_obj_arg, decl: lean_obj_arg) -> lean_obj_res;

    /// Mark the Quot type as initialized
    ///
    /// # Parameters
    /// - `env`: Environment object (consumed)
    ///
    /// # Returns
    /// New environment with Quot marked as initialized
    pub fn lean_environment_mark_quot_init(env: lean_obj_arg) -> lean_obj_res;

    /// Internal: Add a constant info directly to the environment
    ///
    /// This is a low-level function typically not used directly.
    /// Prefer `lean_add_decl` or `lean_add_decl_without_checking`.
    ///
    /// # Parameters
    /// - `env`: Environment object (consumed)
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// New environment with the constant added
    pub fn lean_environment_add(env: lean_obj_arg, cinfo: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Diagnostics
// ============================================================================

extern "C" {
    /// Check if kernel diagnostics are enabled
    ///
    /// # Parameters
    /// - `diag`: Diagnostics object (borrowed)
    ///
    /// # Returns
    /// 0 if disabled, non-zero if enabled
    pub fn lean_kernel_diag_is_enabled(diag: lean_obj_arg) -> u8;

    /// Record an unfold operation in diagnostics
    ///
    /// # Parameters
    /// - `diag`: Diagnostics object (consumed)
    /// - `decl_name`: Name of the declaration being unfolded (borrowed)
    ///
    /// # Returns
    /// New diagnostics object with the unfold recorded
    pub fn lean_kernel_record_unfold(diag: lean_obj_arg, decl_name: lean_obj_arg) -> lean_obj_res;

    /// Get the diagnostics from an environment
    ///
    /// # Parameters
    /// - `env`: Environment object (borrowed)
    ///
    /// # Returns
    /// Diagnostics object
    pub fn lean_kernel_get_diag(env: lean_obj_arg) -> lean_obj_res;

    /// Set the diagnostics for an environment
    ///
    /// # Parameters
    /// - `env`: Environment object (consumed)
    /// - `diag`: Diagnostics object (borrowed)
    ///
    /// # Returns
    /// New environment with updated diagnostics
    pub fn lean_kernel_set_diag(env: lean_obj_arg, diag: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Environment Conversion (Kernel ↔ Elab)
// ============================================================================

extern "C" {
    /// Convert a kernel environment to an elaborator environment
    ///
    /// # Parameters
    /// - `env`: Kernel environment (borrowed)
    ///
    /// # Returns
    /// Elaborator environment
    pub fn lean_elab_environment_of_kernel_env(env: lean_obj_arg) -> lean_obj_res;

    /// Convert an elaborator environment to a kernel environment
    ///
    /// # Parameters
    /// - `env`: Elaborator environment (borrowed)
    ///
    /// # Returns
    /// Kernel environment
    pub fn lean_elab_environment_to_kernel_env(env: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Declaration Construction
// ============================================================================

extern "C" {
    /// Create an axiom declaration
    ///
    /// Axioms are constants assumed without proof.
    ///
    /// # Parameters
    /// - `name`: Name of the axiom (consumed)
    /// - `level_params`: List of universe level parameters (consumed)
    /// - `type_`: Type expression of the axiom (consumed)
    /// - `is_unsafe`: 0 for safe axiom, non-zero for unsafe axiom
    ///
    /// # Returns
    /// Declaration object
    ///
    /// # Lean type
    /// ```lean
    /// axiom_decl : Name → List Name → Expr → Bool → Declaration
    /// ```
    pub fn lean_mk_axiom(
        name: lean_obj_arg,
        level_params: lean_obj_arg,
        type_: lean_obj_arg,
        is_unsafe: u8,
    ) -> lean_obj_res;

    /// Create a definition declaration
    ///
    /// Definitions are constants with computational content.
    ///
    /// # Parameters
    /// - `name`: Name of the definition (consumed)
    /// - `level_params`: List of universe level parameters (consumed)
    /// - `type_`: Type expression (consumed)
    /// - `value`: Value expression (consumed)
    /// - `hints`: Reducibility hints (consumed)
    /// - `safety`: Safety level (0 = safe, 1 = partial, 2 = unsafe)
    ///
    /// # Returns
    /// Declaration object
    pub fn lean_mk_definition(
        name: lean_obj_arg,
        level_params: lean_obj_arg,
        type_: lean_obj_arg,
        value: lean_obj_arg,
        hints: lean_obj_arg,
        safety: u8,
    ) -> lean_obj_res;

    /// Create a theorem declaration
    ///
    /// Theorems are definitions in Prop that are never reduced.
    ///
    /// # Parameters
    /// - `name`: Name of the theorem (consumed)
    /// - `level_params`: List of universe level parameters (consumed)
    /// - `type_`: Type expression (consumed)
    /// - `value`: Proof term (consumed)
    ///
    /// # Returns
    /// Declaration object
    pub fn lean_mk_theorem(
        name: lean_obj_arg,
        level_params: lean_obj_arg,
        type_: lean_obj_arg,
        value: lean_obj_arg,
    ) -> lean_obj_res;
}

// ============================================================================
// ConstantInfo Accessors
// ============================================================================

extern "C" {
    /// Get the name of a constant
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// Name object
    pub fn lean_constant_info_name(cinfo: lean_obj_arg) -> lean_obj_res;

    /// Get the type of a constant
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// Expression representing the type
    pub fn lean_constant_info_type(cinfo: lean_obj_arg) -> lean_obj_res;

    /// Get the universe level parameters of a constant
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// List of level parameter names
    pub fn lean_constant_info_level_params(cinfo: lean_obj_arg) -> lean_obj_res;

    /// Get the kind of a constant
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// Kind as u8:
    /// - 0: Axiom
    /// - 1: Definition
    /// - 2: Theorem
    /// - 3: Opaque
    /// - 4: Quot
    /// - 5: Inductive
    /// - 6: Constructor
    /// - 7: Recursor
    pub fn lean_constant_info_kind(cinfo: lean_obj_arg) -> u8;

    /// Check if a constant has a value (is a definition or theorem)
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// 0 if no value (axiom), non-zero if has value (definition/theorem)
    pub fn lean_constant_info_has_value(cinfo: lean_obj_arg) -> u8;

    /// Get the value of a constant (only valid if has_value returns true)
    ///
    /// # Parameters
    /// - `cinfo`: ConstantInfo object (borrowed)
    ///
    /// # Returns
    /// Expression representing the value
    ///
    /// # Safety
    /// Must check `lean_constant_info_has_value` before calling this
    pub fn lean_constant_info_value(cinfo: lean_obj_arg) -> lean_obj_res;
}

// ============================================================================
// Constants for Constant Kinds
// ============================================================================

/// Constant kind: Axiom
pub const LEAN_CONSTANT_KIND_AXIOM: u8 = 0;
/// Constant kind: Definition
pub const LEAN_CONSTANT_KIND_DEFINITION: u8 = 1;
/// Constant kind: Theorem
pub const LEAN_CONSTANT_KIND_THEOREM: u8 = 2;
/// Constant kind: Opaque definition
pub const LEAN_CONSTANT_KIND_OPAQUE: u8 = 3;
/// Constant kind: Quot type
pub const LEAN_CONSTANT_KIND_QUOT: u8 = 4;
/// Constant kind: Inductive type
pub const LEAN_CONSTANT_KIND_INDUCTIVE: u8 = 5;
/// Constant kind: Constructor
pub const LEAN_CONSTANT_KIND_CONSTRUCTOR: u8 = 6;
/// Constant kind: Recursor
pub const LEAN_CONSTANT_KIND_RECURSOR: u8 = 7;

// ============================================================================
// Safety Levels for Definitions
// ============================================================================

/// Definition safety: Safe (fully type-checked)
pub const LEAN_DEF_SAFETY_SAFE: u8 = 0;
/// Definition safety: Partial (may not terminate)
pub const LEAN_DEF_SAFETY_PARTIAL: u8 = 1;
/// Definition safety: Unsafe (axiom-like)
pub const LEAN_DEF_SAFETY_UNSAFE: u8 = 2;
