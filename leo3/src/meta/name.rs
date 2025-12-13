//! Lean Name type - hierarchical identifiers
//!
//! Names in Lean are hierarchical identifiers used for constants, variables,
//! and other named entities. They are built from components:
//! - Anonymous (root)
//! - String components (like "Nat", "add")
//! - Numeric components
//!
//! # Example
//!
//! ```ignore
//! // Create the name "Nat.add"
//! let name = LeanName::from_str(lean, "Nat")?
//!     .append_str(lean, "add")?;
//! ```

use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::{LeanNat, LeanString};
use crate::LeanResult;
use leo3_ffi as ffi;

/// A Lean Name - hierarchical identifier
///
/// Names are immutable and hierarchical. Common operations:
/// - Create from components: `from_str`, `anonymous`
/// - Append components: `append_str`, `append_num`
/// - Compare: `eq`
#[repr(transparent)]
pub struct LeanName {
    _private: (),
}

impl LeanName {
    /// Create the anonymous (root) name
    ///
    /// This is the empty name that serves as the root of the name hierarchy.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let root = LeanName::anonymous(lean)?;
    /// ```
    pub fn anonymous<'l>(lean: Lean<'l>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Name.anonymous is represented as a SCALAR (lean_box(0)), not a heap object!
            // This is because in the C++ runtime, Name.anonymous is checked via is_scalar().
            // See: lean4/src/util/name.h line 57: static bool is_anonymous(object * o) { return is_scalar(o); }
            let ptr = ffi::lean_box(0);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a simple name from a string
    ///
    /// Creates `Name.str Name.anonymous s`, which is a name with a single component.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let nat_name = LeanName::from_str(lean, "Nat")?;
    /// ```
    pub fn from_str<'l>(lean: Lean<'l>, s: &str) -> LeanResult<LeanBound<'l, Self>> {
        let anonymous = Self::anonymous(lean)?;
        Self::append_str(anonymous, lean, s)
    }

    /// Create a hierarchical name from a dot-separated string
    ///
    /// Parses a string like "Nat.add" into a hierarchical name.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let nat_add = LeanName::from_components(lean, "Nat.add")?;
    /// // Equivalent to: anonymous.append_str("Nat").append_str("add")
    /// ```
    pub fn from_components<'l>(lean: Lean<'l>, path: &str) -> LeanResult<LeanBound<'l, Self>> {
        let mut name = Self::anonymous(lean)?;
        for component in path.split('.').filter(|s| !s.is_empty()) {
            name = Self::append_str(name, lean, component)?;
        }
        Ok(name)
    }

    /// Append a string component to a name
    ///
    /// Creates `Name.str pre s`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let nat = LeanName::from_str(lean, "Nat")?;
    /// let nat_add = LeanName::append_str(nat, lean, "add")?;
    /// ```
    pub fn append_str<'l>(
        pre: LeanBound<'l, Self>,
        lean: Lean<'l>,
        s: &str,
    ) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_prelude_initialized();
        unsafe {
            let str_val = LeanString::mk(lean, s)?;
            let ptr = ffi::name::lean_name_mk_string(pre.into_ptr(), str_val.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Append a numeric component to a name
    ///
    /// Creates `Name.num pre n`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name = LeanName::from_str(lean, "x")?;
    /// let x_1 = LeanName::append_num(name, lean, 1)?;
    /// ```
    pub fn append_num<'l>(
        pre: LeanBound<'l, Self>,
        lean: Lean<'l>,
        n: usize,
    ) -> LeanResult<LeanBound<'l, Self>> {
        super::ensure_prelude_initialized();
        unsafe {
            let num_val = LeanNat::from_usize(lean, n)?;
            let ptr = ffi::name::lean_name_mk_numeral(pre.into_ptr(), num_val.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Check if two names are equal
    ///
    /// # Example
    ///
    /// ```ignore
    /// let name1 = LeanName::from_str(lean, "Nat")?;
    /// let name2 = LeanName::from_str(lean, "Nat")?;
    /// assert!(LeanName::eq(&name1, &name2));
    /// ```
    pub fn eq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { ffi::name::lean_name_eq(a.as_ptr(), b.as_ptr()) != 0 }
    }

    /// Get the name kind
    pub fn kind<'l>(name: &LeanBound<'l, Self>) -> NameKind {
        unsafe {
            let tag = ffi::lean_obj_tag(name.as_ptr());
            NameKind::from_u8(tag)
        }
    }
}

/// Name kind (3 variants)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NameKind {
    /// Anonymous (root) name
    Anonymous,
    /// String component
    Str,
    /// Numeric component
    Num,
}

impl NameKind {
    pub(crate) fn from_u8(val: u8) -> Self {
        match val {
            ffi::name::LEAN_NAME_ANONYMOUS => Self::Anonymous,
            ffi::name::LEAN_NAME_STR => Self::Str,
            ffi::name::LEAN_NAME_NUM => Self::Num,
            _ => panic!("Invalid name kind: {}", val),
        }
    }
}
