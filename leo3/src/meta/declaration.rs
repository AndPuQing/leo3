//! Declaration builders for creating Lean declarations
//!
//! Declarations represent axioms, definitions, theorems, and other constants
//! that can be added to an environment.

use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;
use crate::types::LeanList;
use crate::LeanResult;
use leo3_ffi as ffi;

use super::name::LeanName;

/// Safety level for definitions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    /// Fully type-checked, safe definition
    Safe,
    /// May not terminate (partial definition)
    Partial,
    /// Unsafe definition (axiom-like)
    Unsafe,
}

impl DefinitionSafety {
    fn to_u8(self) -> u8 {
        match self {
            Self::Safe => ffi::environment::LEAN_DEF_SAFETY_SAFE,
            Self::Partial => ffi::environment::LEAN_DEF_SAFETY_PARTIAL,
            Self::Unsafe => ffi::environment::LEAN_DEF_SAFETY_UNSAFE,
        }
    }
}

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
            let axiom_val = ffi::environment::lean_mk_axiom(
                name.into_ptr(),
                level_params.into_ptr(),
                type_.into_ptr(),
                is_unsafe as u8,
            );
            // Wrap AxiomVal in Declaration.axiomDecl (tag 0, 1 obj field)
            let decl = ffi::lean_alloc_ctor(0, 1, 0);
            ffi::lean_ctor_set(decl, 0, axiom_val);
            Ok(LeanBound::from_owned_ptr(lean, decl))
        }
    }

    /// Create a theorem declaration
    ///
    /// Theorems are propositions with proofs. Unlike definitions, theorem values
    /// are never unfolded during type checking.
    ///
    /// # Arguments
    ///
    /// * `lean` - Lean lifetime token
    /// * `name` - Name of the theorem
    /// * `level_params` - List of universe level parameters
    /// * `type_` - Type expression (the proposition)
    /// * `value` - Value expression (the proof)
    pub fn theorem<'l>(
        lean: Lean<'l>,
        name: LeanBound<'l, LeanName>,
        level_params: LeanBound<'l, LeanList>,
        type_: LeanBound<'l, super::expr::LeanExpr>,
        value: LeanBound<'l, super::expr::LeanExpr>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let all = LeanList::cons(name.clone().cast(), LeanList::nil(lean)?)?;
        unsafe {
            let thm_val = ffi::environment::lean_mk_theorem(
                name.into_ptr(),
                level_params.into_ptr(),
                type_.into_ptr(),
                value.into_ptr(),
                all.into_ptr(),
            );
            // Wrap TheoremVal in Declaration.thmDecl (tag 2, 1 obj field)
            let decl = ffi::lean_alloc_ctor(2, 1, 0);
            ffi::lean_ctor_set(decl, 0, thm_val);
            Ok(LeanBound::from_owned_ptr(lean, decl))
        }
    }

    /// Create a definition declaration
    ///
    /// Definitions are constants with computational content that can be unfolded.
    ///
    /// # Arguments
    ///
    /// * `lean` - Lean lifetime token
    /// * `name` - Name of the definition
    /// * `level_params` - List of universe level parameters
    /// * `type_` - Type expression
    /// * `value` - Value expression
    /// * `hints` - Reducibility hints (controls unfolding behavior)
    /// * `safety` - Safety level (safe, partial, or unsafe)
    pub fn definition<'l>(
        lean: Lean<'l>,
        name: LeanBound<'l, LeanName>,
        level_params: LeanBound<'l, LeanList>,
        type_: LeanBound<'l, super::expr::LeanExpr>,
        value: LeanBound<'l, super::expr::LeanExpr>,
        hints: LeanBound<'l, LeanAny>,
        safety: DefinitionSafety,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let all = LeanList::cons(name.clone().cast(), LeanList::nil(lean)?)?;
        unsafe {
            let def_val = ffi::environment::lean_mk_definition(
                name.into_ptr(),
                level_params.into_ptr(),
                type_.into_ptr(),
                value.into_ptr(),
                hints.into_ptr(),
                safety.to_u8(),
                all.into_ptr(),
            );
            // Wrap DefinitionVal in Declaration.defnDecl (tag 1, 1 obj field)
            let decl = ffi::lean_alloc_ctor(1, 1, 0);
            ffi::lean_ctor_set(decl, 0, def_val);
            Ok(LeanBound::from_owned_ptr(lean, decl))
        }
    }
}
