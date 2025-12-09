//! Lean unsigned integer type wrappers.
//!
//! Provides wrappers for UInt8, UInt16, UInt32, and UInt64 types.

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::object::{
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_get_uint8,
    lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_uint8,
};
use crate::instance::LeanBound;
use crate::marker::Lean;

// ============================================================================
// UInt8
// ============================================================================

/// A Lean 8-bit unsigned integer.
pub struct LeanUInt8 {
    _private: (),
}

impl LeanUInt8 {
    /// Create a Lean UInt8 from a Rust u8.
    pub fn mk<'l>(lean: Lean<'l>, value: u8) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 1);
            lean_ctor_set_uint8(ptr, 0, value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust u8.
    pub fn to_u8<'l>(obj: &LeanBound<'l, Self>) -> u8 {
        unsafe { lean_ctor_get_uint8(obj.as_ptr(), 0) }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUInt8> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUInt8({})", LeanUInt8::to_u8(self))
    }
}

// ============================================================================
// UInt16
// ============================================================================

/// A Lean 16-bit unsigned integer.
pub struct LeanUInt16 {
    _private: (),
}

impl LeanUInt16 {
    /// Create a Lean UInt16 from a Rust u16.
    pub fn mk<'l>(lean: Lean<'l>, value: u16) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 2);
            lean_ctor_set_uint16(ptr, 0, value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust u16.
    pub fn to_u16<'l>(obj: &LeanBound<'l, Self>) -> u16 {
        unsafe { lean_ctor_get_uint16(obj.as_ptr(), 0) }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUInt16> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUInt16({})", LeanUInt16::to_u16(self))
    }
}

// ============================================================================
// UInt32
// ============================================================================

/// A Lean 32-bit unsigned integer.
pub struct LeanUInt32 {
    _private: (),
}

impl LeanUInt32 {
    /// Create a Lean UInt32 from a Rust u32.
    pub fn mk<'l>(lean: Lean<'l>, value: u32) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 4);
            lean_ctor_set_uint32(ptr, 0, value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust u32.
    pub fn to_u32<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUInt32> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUInt32({})", LeanUInt32::to_u32(self))
    }
}

// ============================================================================
// UInt64
// ============================================================================

/// A Lean 64-bit unsigned integer.
pub struct LeanUInt64 {
    _private: (),
}

impl LeanUInt64 {
    /// Create a Lean UInt64 from a Rust u64.
    pub fn mk<'l>(lean: Lean<'l>, value: u64) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let ptr = ffi::lean_alloc_ctor(0, 0, 8);
            lean_ctor_set_uint64(ptr, 0, value);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to Rust u64.
    pub fn to_u64<'l>(obj: &LeanBound<'l, Self>) -> u64 {
        unsafe { lean_ctor_get_uint64(obj.as_ptr(), 0) }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUInt64> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUInt64({})", LeanUInt64::to_u64(self))
    }
}

// ============================================================================
// USize (platform-dependent)
// ============================================================================

/// A Lean platform-sized unsigned integer (USize).
pub struct LeanUSize {
    _private: (),
}

impl LeanUSize {
    /// Create a Lean USize from a Rust usize.
    pub fn mk<'l>(lean: Lean<'l>, value: usize) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            if std::mem::size_of::<usize>() == 8 {
                let ptr = ffi::lean_alloc_ctor(0, 0, 8);
                lean_ctor_set_uint64(ptr, 0, value as u64);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            } else {
                let ptr = ffi::lean_alloc_ctor(0, 0, 4);
                lean_ctor_set_uint32(ptr, 0, value as u32);
                Ok(LeanBound::from_owned_ptr(lean, ptr))
            }
        }
    }

    /// Convert to Rust usize.
    pub fn to_usize<'l>(obj: &LeanBound<'l, Self>) -> usize {
        if std::mem::size_of::<usize>() == 8 {
            unsafe { lean_ctor_get_uint64(obj.as_ptr(), 0) as usize }
        } else {
            unsafe { lean_ctor_get_uint32(obj.as_ptr(), 0) as usize }
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUSize> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUSize({})", LeanUSize::to_usize(self))
    }
}
