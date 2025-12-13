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

pub mod declaration;
pub mod environment;
pub mod expr;
pub mod level;
pub mod literal;

// Re-export main types
pub use declaration::LeanDeclaration;
pub use environment::{ConstantKind, LeanConstantInfo, LeanEnvironment};
pub use expr::{BinderInfo, ExprKind, LeanExpr};
pub use level::LeanLevel;
pub use literal::LeanLiteral;
