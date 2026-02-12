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

    /// Create a Lean character from a natural number (codepoint).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.ofNat` in Lean4.
    ///
    /// Returns None if the codepoint is not a valid Unicode scalar value.
    #[allow(non_snake_case)]
    pub fn ofNat<'l>(lean: Lean<'l>, codepoint: u32) -> LeanResult<Option<LeanBound<'l, Self>>> {
        // Check if valid Unicode scalar value
        match char::from_u32(codepoint) {
            Some(c) => Ok(Some(Self::mk(lean, c)?)),
            None => Ok(None),
        }
    }

    /// Create a Lean character from a UInt8.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.ofUInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn ofUInt8<'l>(lean: Lean<'l>, byte: u8) -> LeanResult<LeanBound<'l, Self>> {
        Self::mk(lean, byte as char)
    }

    /// Convert a Lean character to a natural number (codepoint).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.toNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn toNat<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) }
    }

    /// Convert a Lean character to UInt8 (truncating if necessary).
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.toUInt8` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUInt8<'l>(obj: &LeanBound<'l, Self>) -> u8 {
        Self::toNat(obj) as u8
    }

    /// Convert a Lean character to a Rust char.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.val` in Lean4.
    #[allow(non_snake_case)]
    pub fn toChar<'l>(obj: &LeanBound<'l, Self>) -> Option<char> {
        char::from_u32(Self::toNat(obj))
    }

    /// Check if a natural number is a valid Unicode scalar value.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isValidCharNat` in Lean4.
    #[allow(non_snake_case)]
    pub fn isValidCharNat(n: u32) -> bool {
        char::from_u32(n).is_some()
    }

    /// Check if the character is alphabetic.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isAlpha` in Lean4.
    #[allow(non_snake_case)]
    pub fn isAlpha<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_alphabetic())
    }

    /// Check if the character is alphanumeric.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isAlphanum` in Lean4.
    #[allow(non_snake_case)]
    pub fn isAlphanum<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_alphanumeric())
    }

    /// Check if the character is a digit.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isDigit` in Lean4.
    #[allow(non_snake_case)]
    pub fn isDigit<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_ascii_digit())
    }

    /// Check if the character is lowercase.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isLower` in Lean4.
    #[allow(non_snake_case)]
    pub fn isLower<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_lowercase())
    }

    /// Check if the character is uppercase.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isUpper` in Lean4.
    #[allow(non_snake_case)]
    pub fn isUpper<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_uppercase())
    }

    /// Check if the character is whitespace.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.isWhitespace` in Lean4.
    #[allow(non_snake_case)]
    pub fn isWhitespace<'l>(obj: &LeanBound<'l, Self>) -> bool {
        Self::toChar(obj).is_some_and(|c| c.is_whitespace())
    }

    /// Convert to uppercase.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.toUpper` in Lean4.
    #[allow(non_snake_case)]
    pub fn toUpper<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        let c = Self::toChar(&obj).unwrap_or('\0');
        Self::mk(lean, c.to_ascii_uppercase())
    }

    /// Convert to lowercase.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.toLower` in Lean4.
    #[allow(non_snake_case)]
    pub fn toLower<'l>(obj: LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = obj.lean_token();
        let c = Self::toChar(&obj).unwrap_or('\0');
        Self::mk(lean, c.to_ascii_lowercase())
    }

    /// Check if this character is less than or equal to another.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.le` in Lean4.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::toNat(a) <= Self::toNat(b)
    }

    /// Check if this character is less than another.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.lt` in Lean4.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        Self::toNat(a) < Self::toNat(b)
    }

    /// Get the UTF-8 encoded size in bytes.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.utf8Size` in Lean4.
    #[allow(non_snake_case)]
    pub fn utf8Size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        Self::toChar(obj).map_or(0, |c| c.len_utf8())
    }

    /// Get the UTF-16 encoded size in 16-bit code units.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Char.utf16Size` in Lean4.
    #[allow(non_snake_case)]
    pub fn utf16Size<'l>(obj: &LeanBound<'l, Self>) -> usize {
        Self::toChar(obj).map_or(0, |c| c.len_utf16())
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
