//! Lean signed integer type wrappers.
//!
//! Provides wrappers for Int8, Int16, Int32, and Int64 types.
//!
//! In Lean4, these are structures that wrap UInt types using two's complement:
//! ```lean
//! structure Int8 where
//!   ofUInt8 :: toUInt8 : UInt8
//! ```

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::object::{
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_get_uint8,
    lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_uint8,
};
use crate::instance::LeanBound;
use crate::marker::Lean;

// ============================================================================
// Int8
// ============================================================================

/// A Lean 8-bit signed integer.
///
/// In Lean4, this is represented as a structure wrapping UInt8 using two's complement.
pub struct LeanInt8 {
    _private: (),
}

impl LeanInt8 {
    /// Create a Lean Int8 from a Rust i8.
    pub fn mk<'l>(lean: Lean<'l>, value: i8) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Int8 is a structure with one field (toUInt8)
            let ptr = ffi::lean_alloc_ctor(0, 0, 1);
            // Store the two's complement representation as uint8
            lean_ctor_set_uint8(ptr, 0, value as u8);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust i8.
    pub fn to_i8<'l>(obj: &LeanBound<'l, Self>) -> i8 {
        unsafe {
            // Read the two's complement representation
            let uint_val = lean_ctor_get_uint8(obj.as_ptr(), 0);
            uint_val as i8
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt8> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt8({})", LeanInt8::to_i8(self))
    }
}

// ============================================================================
// Int16
// ============================================================================

/// A Lean 16-bit signed integer.
///
/// In Lean4, this is represented as a structure wrapping UInt16 using two's complement.
pub struct LeanInt16 {
    _private: (),
}

impl LeanInt16 {
    /// Create a Lean Int16 from a Rust i16.
    pub fn mk<'l>(lean: Lean<'l>, value: i16) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Int16 is a structure with one field (toUInt16)
            let ptr = ffi::lean_alloc_ctor(0, 0, 2);
            // Store the two's complement representation as uint16
            lean_ctor_set_uint16(ptr, 0, value as u16);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust i16.
    pub fn to_i16<'l>(obj: &LeanBound<'l, Self>) -> i16 {
        unsafe {
            // Read the two's complement representation
            let uint_val = lean_ctor_get_uint16(obj.as_ptr(), 0);
            uint_val as i16
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt16> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt16({})", LeanInt16::to_i16(self))
    }
}

// ============================================================================
// Int32
// ============================================================================

/// A Lean 32-bit signed integer.
///
/// In Lean4, this is represented as a structure wrapping UInt32 using two's complement.
pub struct LeanInt32 {
    _private: (),
}

impl LeanInt32 {
    /// Create a Lean Int32 from a Rust i32.
    pub fn mk<'l>(lean: Lean<'l>, value: i32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Int32 is a structure with one field (toUInt32)
            let ptr = ffi::lean_alloc_ctor(0, 0, 4);
            // Store the two's complement representation as uint32
            lean_ctor_set_uint32(ptr, 0, value as u32);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust i32.
    pub fn to_i32<'l>(obj: &LeanBound<'l, Self>) -> i32 {
        unsafe {
            // Read the two's complement representation
            let uint_val = lean_ctor_get_uint32(obj.as_ptr(), 0);
            uint_val as i32
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt32> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt32({})", LeanInt32::to_i32(self))
    }
}

// ============================================================================
// Int64
// ============================================================================

/// A Lean 64-bit signed integer.
///
/// In Lean4, this is represented as a structure wrapping UInt64 using two's complement.
pub struct LeanInt64 {
    _private: (),
}

impl LeanInt64 {
    /// Create a Lean Int64 from a Rust i64.
    pub fn mk<'l>(lean: Lean<'l>, value: i64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            // Int64 is a structure with one field (toUInt64)
            let ptr = ffi::lean_alloc_ctor(0, 0, 8);
            // Store the two's complement representation as uint64
            lean_ctor_set_uint64(ptr, 0, value as u64);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust i64.
    pub fn to_i64<'l>(obj: &LeanBound<'l, Self>) -> i64 {
        unsafe {
            // Read the two's complement representation
            let uint_val = lean_ctor_get_uint64(obj.as_ptr(), 0);
            uint_val as i64
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanInt64> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanInt64({})", LeanInt64::to_i64(self))
    }
}

// ============================================================================
// ISize (platform-dependent)
// ============================================================================

/// A Lean platform-sized signed integer (ISize).
///
/// In Lean4, this is represented as a structure wrapping USize using two's complement.
pub struct LeanISize {
    _private: (),
}

impl LeanISize {
    /// Create a Lean ISize from a Rust isize.
    pub fn mk<'l>(lean: Lean<'l>, value: isize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            if std::mem::size_of::<isize>() == 8 {
                // ISize is a structure with one field (toUSize)
                let ptr = ffi::lean_alloc_ctor(0, 0, 8);
                // Store the two's complement representation as uint64
                lean_ctor_set_uint64(ptr, 0, value as u64);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            } else {
                // ISize is a structure with one field (toUSize)
                let ptr = ffi::lean_alloc_ctor(0, 0, 4);
                // Store the two's complement representation as uint32
                lean_ctor_set_uint32(ptr, 0, value as u32);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            }
        }
    }

    /// Convert to Rust isize.
    pub fn to_isize<'l>(obj: &LeanBound<'l, Self>) -> isize {
        if std::mem::size_of::<isize>() == 8 {
            unsafe {
                let uint_val = lean_ctor_get_uint64(obj.as_ptr(), 0);
                uint_val as isize
            }
        } else {
            unsafe {
                let uint_val = lean_ctor_get_uint32(obj.as_ptr(), 0);
                uint_val as isize
            }
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanISize> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanISize({})", LeanISize::to_isize(self))
    }
}
