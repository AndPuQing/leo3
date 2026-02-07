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
/// On macOS, we skip the Lean.Expr initialization as it can cause segfaults
/// on some Lean versions (e.g., 4.20.0). The null pointer checks in the
/// functions provide safety even without initialization.
#[inline]
pub(crate) fn ensure_expr_initialized() {
    ensure_prelude_initialized(); // Expr depends on Prelude

    // Skip Lean.Expr initialization on macOS due to compatibility issues
    #[cfg(not(target_os = "macos"))]
    {
        EXPR_INIT.call_once(|| unsafe {
            ffi::initialize_Lean_Expr(1, std::ptr::null_mut());
        });
    }
}

pub mod declaration;
pub mod environment;
pub mod expr;
pub mod level;
pub mod literal;
pub mod name;

// Re-export main types
pub use declaration::LeanDeclaration;
pub use environment::{ConstantKind, LeanConstantInfo, LeanEnvironment};
pub use expr::{BinderInfo, ExprKind, LeanExpr};
pub use level::LeanLevel;
pub use literal::LeanLiteral;
pub use name::{LeanName, NameKind};
