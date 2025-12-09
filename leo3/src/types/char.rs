//! Lean character type wrapper.

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::object::{lean_ctor_get_uint32, lean_ctor_set_uint32};
use crate::instance::LeanBound;
use crate::marker::Lean;

/// A Lean character object.
///
/// Characters in Lean4 are defined as:
/// ```lean
/// structure Char where
///   val : UInt32    -- Unicode scalar value
///   valid : val.isValidChar
/// ```
///
/// Lean characters represent Unicode scalar values.
pub struct LeanChar {
    _private: (),
}

impl LeanChar {
    /// Create a Lean character from a Rust char.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.ofNat` in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let c = LeanChar::mk(lean, 'A')?;
    ///     assert_eq!(LeanChar::toChar(&c), Some('A'));
    ///     Ok(())
    /// })
    /// ```
    pub fn mk<'l>(lean: Lean<'l>, c: char) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Char is a structure with a UInt32 value
            // Tag 0 for structures, 1 field (the uint32 value), 4 bytes for the scalar
            let ptr = ffi::lean_alloc_ctor(0, 0, 4);

            // Set the UInt32 value (char codepoint)
            lean_ctor_set_uint32(ptr, 0, c as u32);

            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Lean character from a u32 codepoint.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.ofNat` in Lean4.
    ///
    /// Returns None if the codepoint is not a valid Unicode scalar value.
    pub fn from_u32<'l>(lean: Lean<'l>, codepoint: u32) -> LeanResult<Option<LeanBound<'l, Self>>> {
        // Check if valid Unicode scalar value
        match char::from_u32(codepoint) {
            Some(c) => Ok(Some(Self::mk(lean, c)?)),
            None => Ok(None),
        }
    }

    /// Convert a Lean character to a Rust char.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.val` in Lean4.
    #[allow(non_snake_case)]
    pub fn toChar<'l>(obj: &LeanBound<'l, Self>) -> Option<char> {
        unsafe {
            // Get the UInt32 value from the structure
            let codepoint = lean_ctor_get_uint32(obj.as_ptr(), 0);
            char::from_u32(codepoint)
        }
    }

    /// Get the Unicode codepoint value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.val` in Lean4.
    pub fn to_u32<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) }
    }

    /// Check if the character is ASCII.
    ///
    /// # Lean4 Reference
    /// Similar to checking if `Char.val < 128` in Lean4.
    #[allow(non_snake_case)]
    pub fn isAscii<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::to_u32(obj) < 128
    }

    /// Check if the character is alphabetic.
    pub fn is_alphabetic<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).map_or(false, |c| c.is_alphabetic())
    }

    /// Check if the character is numeric.
    pub fn is_numeric<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).map_or(false, |c| c.is_numeric())
    }

    /// Check if the character is whitespace.
    pub fn is_whitespace<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).map_or(false, |c| c.is_whitespace())
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanChar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match LeanChar::toChar(self) {
            Some(c) => write!(f, "LeanChar('{}')", c),
            None => write!(f, "LeanChar(<invalid>)"),
        }
    }
}
