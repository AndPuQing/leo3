//! High-level wrapper for Lean's Environment
//!
//! Environments are the core of Lean's module system, storing all declarations,
//! constants, inductive types, and type class instances. Environments are immutable -
//! all modifications return a new environment.

use crate::err::LeanError;
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanList, LeanOption, LeanString};
use crate::LeanResult;
use leo3_ffi as ffi;

// TODO: Implement proper LeanName type wrapper
// For now, using LeanString as a placeholder
type LeanName = LeanString;

/// Lean environment - immutable collection of declarations
///
/// Environments store:
/// - Constants (axioms, definitions, theorems)
/// - Inductive types and constructors
/// - Type class instances
/// - Attributes and metadata
///
/// All modifications create a new environment (immutable updates).
///
/// # Example
///
/// ```ignore
/// use leo3::prelude::*;
/// use leo3::meta::*;
///
/// leo3::with_lean(|lean| {
///     // Create empty environment
///     let env = LeanEnvironment::empty(lean, 0)?;
///
///     // Find a constant
///     let nat_name = LeanName::from_str(lean, "Nat")?;
///     if let Some(cinfo) = LeanEnvironment::find(&env, &nat_name)? {
///         println!("Found Nat with type: {:?}", LeanConstantInfo::type_(&cinfo)?);
///     }
///
///     Ok(())
/// })
/// ```
#[repr(transparent)]
pub struct LeanEnvironment {
    _private: (),
}

impl LeanEnvironment {
    /// Create a new empty environment
    ///
    /// # Arguments
    ///
    /// * `lean` - Lean lifetime token
    /// * `trust_level` - Type checking trust level:
    ///   - `0` = Full type checking (safest, slowest)
    ///   - Higher values = Skip certain checks (faster, less safe)
    ///
    /// # Returns
    ///
    /// New empty environment
    ///
    /// # Example
    ///
    /// ```ignore
    /// let env = LeanEnvironment::empty(lean, 0)?;
    /// ```
    pub fn empty<'l>(lean: Lean<'l>, trust_level: u32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Call FFI to create environment (returns IO Environment)
            let io_result = ffi::environment::lean_mk_empty_environment(trust_level);

            // Check if IO operation succeeded
            // IO results are Except types: tag 1 = error, tag 0 = ok
            let tag = ffi::lean_obj_tag(io_result);
            if tag == 1 {
                // Extract error message (field 0 of Except.error)
                let err_ptr = ffi::lean_ctor_get(io_result, 0) as *mut ffi::lean_object;
                ffi::lean_inc(err_ptr);
                ffi::lean_dec(io_result);

                // TODO: Convert error object to string message
                return Err(LeanError::runtime(
                    "Failed to create empty environment: IO error",
                ));
            }

            // Extract the environment from IO result (field 0 of Except.ok)
            let env_ptr = ffi::lean_ctor_get(io_result, 0) as *mut ffi::lean_object;
            ffi::lean_inc(env_ptr);
            ffi::lean_dec(io_result);

            Ok(LeanBound::from_owned_ptr(lean, env_ptr))
        }
    }

    /// Find a constant by name in the environment
    ///
    /// # Arguments
    ///
    /// * `env` - Environment to search (borrowed)
    /// * `name` - Name of the constant to find
    ///
    /// # Returns
    ///
    /// `Some(ConstantInfo)` if found, `None` if not found
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name = LeanName::from_str(lean, "Nat.add")?;
    /// if let Some(cinfo) = LeanEnvironment::find(&env, &name)? {
    ///     println!("Found: {:?}", LeanConstantInfo::name(&cinfo)?);
    /// }
    /// ```
    pub fn find<'l>(
        env: &LeanBound<'l, Self>,
        name: &LeanBound<'l, LeanName>,
    ) -> LeanResult<Option<LeanBound<'l, LeanConstantInfo>>> {
        unsafe {
            let lean = env.lean_token();
            let result = ffi::environment::lean_environment_find(env.as_ptr(), name.as_ptr());

            // Result is Option ConstantInfo
            let option = LeanBound::<LeanOption>::from_owned_ptr(lean, result);

            // Check if option is None by checking constructor tag
            // Option.none is tag 0, Option.some is tag 1
            let tag = ffi::lean_obj_tag(option.as_ptr());
            if tag == 0 {
                Ok(None)
            } else {
                // Extract the Some value (field 0)
                let cinfo_ptr = ffi::lean_ctor_get(option.as_ptr(), 0) as *mut ffi::lean_object;
                ffi::lean_inc(cinfo_ptr); // Increment refcount since we're returning it
                Ok(Some(LeanBound::from_owned_ptr(lean, cinfo_ptr)))
            }
        }
    }

    /// Check if the Quot type has been initialized in the environment
    ///
    /// # Arguments
    ///
    /// * `env` - Environment to check
    ///
    /// # Returns
    ///
    /// `true` if Quot is initialized, `false` otherwise
    pub fn is_quot_init<'l>(env: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::environment::lean_environment_quot_init(env.as_ptr()) != 0 }
    }

    /// Mark the Quot type as initialized
    ///
    /// # Arguments
    ///
    /// * `env` - Environment to modify (consumed)
    ///
    /// # Returns
    ///
    /// New environment with Quot marked as initialized
    pub fn mark_quot_init<'l>(env: LeanBound<'l, Self>) -> LeanBound<'l, Self> {
        unsafe {
            let lean = env.lean_token();
            let ptr = ffi::environment::lean_environment_mark_quot_init(env.into_ptr());
            LeanBound::from_owned_ptr(lean, ptr)
        }
    }
}

/// Information about a constant in the environment
///
/// Constants include axioms, definitions, theorems, inductive types, constructors, etc.
#[repr(transparent)]
pub struct LeanConstantInfo {
    _private: (),
}

impl LeanConstantInfo {
    /// Get the name of the constant
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name = LeanConstantInfo::name(&cinfo)?;
    /// println!("Constant name: {:?}", name);
    /// ```
    pub fn name<'l>(cinfo: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanName>> {
        unsafe {
            let lean = cinfo.lean_token();
            let ptr = ffi::environment::lean_constant_info_name(cinfo.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the type of the constant
    ///
    /// # Example
    ///
    /// ```ignore
    /// let type_expr = LeanConstantInfo::type_(&cinfo)?;
    /// ```
    pub fn type_<'l>(
        cinfo: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, super::expr::LeanExpr>> {
        unsafe {
            let lean = cinfo.lean_token();
            let ptr = ffi::environment::lean_constant_info_type(cinfo.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the universe level parameters of the constant
    ///
    /// # Example
    ///
    /// ```ignore
    /// let level_params = LeanConstantInfo::level_params(&cinfo)?;
    /// ```
    pub fn level_params<'l>(cinfo: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanList>> {
        unsafe {
            let lean = cinfo.lean_token();
            let ptr = ffi::environment::lean_constant_info_level_params(cinfo.as_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Get the kind of the constant
    ///
    /// # Example
    ///
    /// ```ignore
    /// match LeanConstantInfo::kind(&cinfo) {
    ///     ConstantKind::Axiom => println!("This is an axiom"),
    ///     ConstantKind::Definition => println!("This is a definition"),
    ///     ConstantKind::Theorem => println!("This is a theorem"),
    ///     _ => println!("Other kind"),
    /// }
    /// ```
    pub fn kind<'l>(cinfo: &LeanBound<'l, Self>) -> ConstantKind {
        unsafe {
            let kind_u8 = ffi::environment::lean_constant_info_kind(cinfo.as_ptr());
            ConstantKind::from_u8(kind_u8)
        }
    }

    /// Check if the constant has a value (is a definition or theorem)
    ///
    /// # Returns
    ///
    /// `true` if the constant has a value, `false` for axioms
    pub fn has_value<'l>(cinfo: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::environment::lean_constant_info_has_value(cinfo.as_ptr()) != 0 }
    }

    /// Get the value of the constant (only valid if `has_value` returns true)
    ///
    /// # Returns
    ///
    /// `Some(expr)` if the constant has a value (definition/theorem),
    /// `None` if it doesn't (axiom)
    ///
    /// # Example
    ///
    /// ```ignore
    /// if let Some(value) = LeanConstantInfo::value(&cinfo)? {
    ///     println!("Definition value: {:?}", value);
    /// }
    /// ```
    pub fn value<'l>(
        cinfo: &LeanBound<'l, Self>,
    ) -> LeanResult<Option<LeanBound<'l, super::expr::LeanExpr>>> {
        if !Self::has_value(cinfo) {
            return Ok(None);
        }

        unsafe {
            let lean = cinfo.lean_token();
            let ptr = ffi::environment::lean_constant_info_value(cinfo.as_ptr());
            Ok(Some(LeanBound::from_owned_ptr(lean, ptr)))
        }
    }
}

/// The kind of a constant in the environment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstantKind {
    /// Axiom: assumed without proof
    Axiom,
    /// Definition: constant with computational content
    Definition,
    /// Theorem: proved proposition (never reduced)
    Theorem,
    /// Opaque definition: definition that won't be unfolded
    Opaque,
    /// Quot: quotient type
    Quot,
    /// Inductive type declaration
    Inductive,
    /// Constructor of an inductive type
    Constructor,
    /// Recursor for an inductive type
    Recursor,
}

impl ConstantKind {
    /// Convert from FFI u8 representation
    pub(crate) fn from_u8(val: u8) -> Self {
        match val {
            ffi::environment::LEAN_CONSTANT_KIND_AXIOM => Self::Axiom,
            ffi::environment::LEAN_CONSTANT_KIND_DEFINITION => Self::Definition,
            ffi::environment::LEAN_CONSTANT_KIND_THEOREM => Self::Theorem,
            ffi::environment::LEAN_CONSTANT_KIND_OPAQUE => Self::Opaque,
            ffi::environment::LEAN_CONSTANT_KIND_QUOT => Self::Quot,
            ffi::environment::LEAN_CONSTANT_KIND_INDUCTIVE => Self::Inductive,
            ffi::environment::LEAN_CONSTANT_KIND_CONSTRUCTOR => Self::Constructor,
            ffi::environment::LEAN_CONSTANT_KIND_RECURSOR => Self::Recursor,
            _ => Self::Axiom, // Fallback for unknown values
        }
    }

    /// Convert to FFI u8 representation
    #[allow(dead_code)]
    pub(crate) fn to_u8(self) -> u8 {
        match self {
            Self::Axiom => ffi::environment::LEAN_CONSTANT_KIND_AXIOM,
            Self::Definition => ffi::environment::LEAN_CONSTANT_KIND_DEFINITION,
            Self::Theorem => ffi::environment::LEAN_CONSTANT_KIND_THEOREM,
            Self::Opaque => ffi::environment::LEAN_CONSTANT_KIND_OPAQUE,
            Self::Quot => ffi::environment::LEAN_CONSTANT_KIND_QUOT,
            Self::Inductive => ffi::environment::LEAN_CONSTANT_KIND_INDUCTIVE,
            Self::Constructor => ffi::environment::LEAN_CONSTANT_KIND_CONSTRUCTOR,
            Self::Recursor => ffi::environment::LEAN_CONSTANT_KIND_RECURSOR,
        }
    }
}

impl std::fmt::Display for ConstantKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Axiom => write!(f, "axiom"),
            Self::Definition => write!(f, "def"),
            Self::Theorem => write!(f, "theorem"),
            Self::Opaque => write!(f, "opaque"),
            Self::Quot => write!(f, "quot"),
            Self::Inductive => write!(f, "inductive"),
            Self::Constructor => write!(f, "constructor"),
            Self::Recursor => write!(f, "recursor"),
        }
    }
}
