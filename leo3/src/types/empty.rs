//! Lean empty type wrapper.
//!
//! The `Empty` type is an uninhabited type with no constructors. It represents
//! logical impossibility or contradictions.

use crate::instance::{LeanAny, LeanBound};
use crate::marker::Lean;

/// A Lean empty object.
///
/// The Empty type in Lean4 is inductively defined with no constructors:
/// ```lean
/// inductive Empty : Type
/// ```
///
/// This type is uninhabited - it is impossible to construct a value of type `Empty`.
/// The only operation on `Empty` is elimination (`Empty.elim`), which implements
/// the principle of explosion: from a contradiction, anything follows.
///
/// # Usage
///
/// In Lean4, `Empty` is used to represent impossible cases in pattern matching
/// or to derive any conclusion from a contradictory hypothesis.
///
/// # Runtime Representation
///
/// Since `Empty` has no constructors, there is no runtime representation for this type.
/// It exists purely at the type level for logical reasoning.
pub struct LeanEmpty {
    _private: (),
}

impl LeanEmpty {
    /// Elimination principle for Empty (ex falso quodlibet).
    ///
    /// From a value of type `Empty`, any conclusion can be derived.
    /// This is also known as the principle of explosion.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Empty.elim` in Lean4:
    /// ```lean
    /// def Empty.elim {C : Sort u} : Empty → C := Empty.rec
    /// ```
    ///
    /// # Safety
    ///
    /// This function can never actually be called in safe code since it's impossible
    /// to construct a value of type `Empty`. If this function is somehow called,
    /// it indicates undefined behavior (similar to reaching unreachable code).
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // This example cannot actually run since you cannot construct an Empty value
    /// use leo3::prelude::*;
    ///
    /// fn impossible_function<'l>(lean: Lean<'l>, empty: LeanBound<'l, LeanEmpty>)
    ///     -> LeanBound<'l, LeanAny>
    /// {
    ///     // From Empty, we can derive anything
    ///     LeanEmpty::elim(lean, empty)
    /// }
    /// ```
    pub fn elim<'l>(_lean: Lean<'l>, _empty: LeanBound<'l, Self>) -> LeanBound<'l, LeanAny> {
        // This function should never be called since Empty has no constructors.
        // If we reach here, it's undefined behavior.
        // We use unreachable! to indicate this code path should never execute.
        unreachable!("Empty.elim called: this indicates undefined behavior")
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanEmpty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanEmpty::<!>")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_type_exists() {
        // We can't actually test Empty since we can't construct it,
        // but we can verify the type exists and compiles
        let _marker: Option<LeanEmpty> = None;
    }

    #[test]
    fn test_empty_size() {
        // Verify that LeanEmpty is zero-sized
        assert_eq!(std::mem::size_of::<LeanEmpty>(), 0);
    }
}
