//! Declaration builders for creating Lean declarations
//!
//! Declarations represent axioms, definitions, theorems, and other constants
//! that can be added to an environment.

use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanList, LeanString};
use crate::LeanResult;
use leo3_ffi as ffi;

// TODO: Implement proper LeanName type wrapper
type LeanName = LeanString;

/// Lean declaration (axiom, definition, theorem, etc.)
///
/// Declarations can be added to an environment using `LeanEnvironment::add_decl`.
#[repr(transparent)]
pub struct LeanDeclaration {
    _private: (),
}

impl LeanDeclaration {
    /// Create an axiom declaration
    ///
    /// Axioms are constants assumed without proof.
    ///
    /// # Arguments
    ///
    /// * `lean` - Lean lifetime token
    /// * `name` - Name of the axiom
    /// * `level_params` - List of universe level parameters
    /// * `type_` - Type expression of the axiom
    /// * `is_unsafe` - Whether this is an unsafe axiom
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name = LeanName::from_str(lean, "myAxiom")?;
    /// let level_params = LeanList::nil(lean)?;
    /// let type_ = /* ... construct type expression ... */;
    /// let decl = LeanDeclaration::axiom(lean, name, level_params, type_, false)?;
    /// ```
    pub fn axiom<'l>(
        lean: Lean<'l>,
        name: LeanBound<'l, LeanName>,
        level_params: LeanBound<'l, LeanList>,
        type_: LeanBound<'l, super::expr::LeanExpr>,
        is_unsafe: bool,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::environment::lean_mk_axiom(
                name.into_ptr(),
                level_params.into_ptr(),
                type_.into_ptr(),
                is_unsafe as u8,
            );
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // TODO: Add definition, theorem, and other declaration builders
    // These will be implemented as needed
}
