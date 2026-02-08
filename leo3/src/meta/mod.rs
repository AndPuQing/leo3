//! Meta-programming module for Leo3
//!
//! This module provides high-level Rust APIs for Lean's meta-programming capabilities,
//! enabling programmatic manipulation of Lean environments and expressions.
//!
//! # Core Types
//!
//! - [`LeanEnvironment`] - Immutable collection of declarations (axioms, definitions, theorems)
//! - [`LeanExpr`] - Lean expressions (the core term language)
//! - [`LeanDeclaration`] - Declaration builders
//! - [`LeanLevel`] - Universe levels
//! - [`LeanLiteral`] - Literal values (Nat, String)
//!
//! # Use Cases
//!
//! - **Code generation**: Build Lean code programmatically from Rust
//! - **DSL compilation**: Translate domain-specific languages to Lean
//! - **Proof automation**: Generate proof terms programmatically
//! - **Static analysis**: Inspect and analyze Lean code
//! - **IDE support**: Power language servers and refactoring tools
//!
//! # Example
//!
//! ```ignore
//! use leo3::prelude::*;
//! use leo3::meta::*;
//!
//! leo3::with_lean(|lean| {
//!     // Create an empty environment
//!     let env = LeanEnvironment::empty(lean, 0)?;
//!
//!     // Build a simple expression: λ x : Nat, x
//!     let x_name = LeanName::from_str(lean, "x")?;
//!     let nat_const = LeanExpr::const_(
//!         lean,
//!         LeanName::from_str(lean, "Nat")?,
//!         LeanList::nil(lean)?
//!     )?;
//!     let body = LeanExpr::bvar(lean, 0)?; // Variable 0 refers to x
//!     let lambda = LeanExpr::lambda(
//!         x_name,
//!         nat_const,
//!         body,
//!         BinderInfo::Default
//!     )?;
//!
//!     println!("Created lambda: {:?}", LeanExpr::dbg_to_string(&lambda)?);
//!
//!     Ok(())
//! })?;
//! ```

use leo3_ffi as ffi;
use std::sync::Once;

// ============================================================================
// Lazy Initialization
// ============================================================================

static PRELUDE_INIT: Once = Once::new();
static EXPR_INIT: Once = Once::new();
static ENV_INIT: Once = Once::new();

/// Ensure Init.Prelude module is initialized (for Name functions)
///
/// This is called lazily when Name-related functions are first used.
/// Safe to call multiple times - initialization happens only once.
#[inline]
pub(crate) fn ensure_prelude_initialized() {
    PRELUDE_INIT.call_once(|| unsafe {
        ffi::initialize_Init_Prelude(1, std::ptr::null_mut());
    });
}

/// Ensure Lean.Expr module is initialized (for metaprogramming functions)
///
/// This is called lazily when Expr-related functions are first used.
/// Safe to call multiple times - initialization happens only once.
/// Note: This depends on Init.Prelude, so it initializes that first.
///
/// **Lean 4.20.0 Compatibility**: On macOS with Lean 4.20.0, there was a bug
/// where `initialize_Lean_Expr` incorrectly initialized `l_Lean_levelZero` to 0x1
/// (a tagged immediate) but `lean_level_mk_zero` expected it to be a heap pointer.
/// This has been fixed by overriding `lean_level_mk_zero` in the FFI layer to
/// return 0x1 directly, matching the behavior of Lean 4.27.0+.
#[inline]
pub(crate) fn ensure_expr_initialized() {
    ensure_prelude_initialized(); // Expr depends on Prelude

    EXPR_INIT.call_once(|| unsafe {
        ffi::initialize_Lean_Expr(1, std::ptr::null_mut());
    });
}

/// Ensure Lean.Environment module is initialized (for environment functions)
///
/// This is called lazily when Environment-related functions are first used.
/// Safe to call multiple times - initialization happens only once.
/// Note: This depends on Init.Prelude and Lean.Expr, so it initializes those first.
/// `initialize_Lean_Environment` recursively initializes all transitive dependencies
/// (each guarded by its own `_G_initialized` flag).
#[inline]
pub(crate) fn ensure_environment_initialized() {
    ensure_expr_initialized(); // Environment depends on Expr

    ENV_INIT.call_once(|| unsafe {
        ffi::initialize_Lean_Environment(1, std::ptr::null_mut());
        // Initialize Lean.Meta before marking end of initialization,
        // since Meta functions (inferType, check) need their module
        // globals set up during the initialization phase.
        ffi::initialize_Lean_Meta(1, std::ptr::null_mut());
        // Mark initialization as complete so IO operations like
        // lean_mk_empty_environment can proceed
        ffi::lean_io_mark_end_initialization();
    });
}

/// Ensure Lean.Meta module is initialized (for MetaM functions)
///
/// This is called lazily when MetaM-related functions are first used
/// (e.g., `inferType`, `check`). Safe to call multiple times.
/// Note: Meta initialization is handled inside `ensure_environment_initialized()`
/// to ensure it runs before `lean_io_mark_end_initialization()`.
#[inline]
pub(crate) fn ensure_meta_initialized() {
    ensure_environment_initialized();
}

pub mod context;
pub mod declaration;
pub mod environment;
pub mod expr;
pub mod level;
pub mod literal;
pub mod metam;
pub mod name;

// Re-export main types
pub use context::{CoreContext, CoreState, MetaContext, MetaState};
pub use declaration::{DefinitionSafety, LeanDeclaration};
pub use environment::{ConstantKind, LeanConstantInfo, LeanEnvironment};
pub use expr::{BinderInfo, ExprKind, LeanExpr};
pub use level::LeanLevel;
pub use literal::LeanLiteral;
pub use metam::MetaMContext;
pub use name::{LeanName, NameKind};
