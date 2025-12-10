//! Lean unsigned integer type wrappers.
//!
//! Provides wrappers for UInt8, UInt16, UInt32, UInt64, and USize types.

use crate::err::LeanResult;
use crate::ffi;
use crate::ffi::inline::*;
use crate::ffi::object::{
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_get_uint8,
    lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_ctor_set_uint8,
};
use crate::instance::LeanBound;
use crate::marker::Lean;
use crate::types::LeanChar;

// ============================================================================
// UInt8
// ============================================================================

/// A Lean 8-bit unsigned integer.
pub struct LeanUInt8 {
    _private: (),
}

#[allow(non_snake_case, missing_docs)]
impl LeanUInt8 {
    /// The number of distinct values: 2^8 = 256.
    pub const SIZE: u32 = 256;

    /// The minimum value: 0.
    pub const MIN: u8 = 0;

    /// The maximum value: 2^8 - 1 = 255.
    pub const MAX: u8 = 255;

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

    // Arithmetic operations

    /// Addition with wrapping semantics.
    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_add(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Subtraction with wrapping semantics.
    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_sub(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Multiplication with wrapping semantics.
    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_mul(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Division. Returns 0 if divisor is 0.
    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_div(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Modulo operation. Returns dividend if divisor is 0.
    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_mod(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Negation with wrapping semantics.
    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_neg(Self::to_u8(a));
            Self::mk(lean, result)
        }
    }

    // Bitwise operations

    /// Bitwise AND.
    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_land(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Bitwise OR.
    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_lor(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Bitwise XOR.
    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_xor(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Bitwise complement (NOT).
    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_complement(Self::to_u8(a));
            Self::mk(lean, result)
        }
    }

    /// Left shift.
    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_shift_left(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    /// Right shift.
    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint8_shift_right(Self::to_u8(a), Self::to_u8(b));
            Self::mk(lean, result)
        }
    }

    // Comparison operations

    /// Check equality.
    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint8_dec_eq(Self::to_u8(a), Self::to_u8(b)) }
    }

    /// Check if strictly less than.
    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint8_dec_lt(Self::to_u8(a), Self::to_u8(b)) }
    }

    /// Check if less than or equal.
    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint8_dec_le(Self::to_u8(a), Self::to_u8(b)) }
    }

    // Character operations

    /// Check if this value is a valid Unicode scalar.
    /// For UInt8, all values are valid Unicode scalars.
    pub fn isValidChar<'l>(_obj: &LeanBound<'l, Self>) -> bool {
        true
    }

    /// Convert to LeanChar. Always succeeds for UInt8.
    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_u8(obj) as u32;
        let c = char::from_u32(val).expect("UInt8 values are always valid Unicode scalars");
        LeanChar::mk(lean, c)
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        // Convert through Nat since unsigned values are always non-negative
        let nat = Self::toNat(obj, lean)?;
        crate::types::LeanInt::ofNat(lean, nat)
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        // For UInt8.ofInt, Lean4 does: ofNat ((x % 2^8).toNat)
        // We'll use a simpler approach: extract to i64, cast to u8 (wrapping)
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as u8;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (arbitrary precision natural number).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        unsafe {
            let val = Self::to_u8(obj);
            let ptr = ffi::inline::lean_uint8_to_nat(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint8_of_nat(nat.as_ptr());
            Self::mk(lean, val)
        }
    }

    /// Create from LeanNat with explicit truncation (same as ofNat).
    pub fn ofNatTruncate<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    /// Create from LeanNat with proof that value is less than size.
    /// In FFI context, this is the same as ofNat since we can't verify the proof.
    pub fn ofNatLT<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    // Comparison operations (non-decidable versions)

    /// Less than or equal comparison.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint8_dec_le(Self::to_u8(a), Self::to_u8(b)) }
    }

    /// Less than comparison.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint8_dec_lt(Self::to_u8(a), Self::to_u8(b)) }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_u8(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to LeanFloat32 (32-bit float).
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let val = lean_uint8_to_float32(Self::to_u8(obj));
            let ptr = ffi::inline::lean_box_float32(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // UInt conversions

    /// Convert to LeanUInt16.
    pub fn toUInt16<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt16>> {
        unsafe {
            let val = lean_uint8_to_uint16(Self::to_u8(obj));
            LeanUInt16::mk(lean, val)
        }
    }

    /// Convert to LeanUInt32.
    pub fn toUInt32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt32>> {
        unsafe {
            let val = lean_uint8_to_uint32(Self::to_u8(obj));
            LeanUInt32::mk(lean, val)
        }
    }

    /// Convert to LeanUInt64.
    pub fn toUInt64<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt64>> {
        unsafe {
            let val = lean_uint8_to_uint64(Self::to_u8(obj));
            LeanUInt64::mk(lean, val)
        }
    }

    /// Convert to LeanUSize.
    pub fn toUSize<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUSize>> {
        unsafe {
            let val = lean_uint8_to_usize(Self::to_u8(obj));
            LeanUSize::mk(lean, val)
        }
    }

    // Special operations

    /// Compute floor(log2(n)). Returns 0 for n = 0.
    pub fn log2<'l>(obj: &LeanBound<'l, Self>) -> u8 {
        let val = Self::to_u8(obj);
        if val == 0 {
            0
        } else {
            7 - val.leading_zeros() as u8
        }
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

#[allow(non_snake_case, missing_docs)]
impl LeanUInt16 {
    /// The number of distinct values: 2^16 = 65536.
    pub const SIZE: u32 = 65536;

    /// The minimum value: 0.
    pub const MIN: u16 = 0;

    /// The maximum value: 2^16 - 1 = 65535.
    pub const MAX: u16 = 65535;

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

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_add(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_sub(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_mul(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_div(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_mod(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_neg(Self::to_u16(a));
            Self::mk(lean, result)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_land(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_lor(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_xor(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_complement(Self::to_u16(a));
            Self::mk(lean, result)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_shift_left(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint16_shift_right(Self::to_u16(a), Self::to_u16(b));
            Self::mk(lean, result)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint16_dec_eq(Self::to_u16(a), Self::to_u16(b)) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint16_dec_lt(Self::to_u16(a), Self::to_u16(b)) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint16_dec_le(Self::to_u16(a), Self::to_u16(b)) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_u16(obj) as u32;
        val < 0xD800 || (0xE000..=0x10FFFF).contains(&val)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_u16(obj) as u32;
        match char::from_u32(val) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        let nat = Self::toNat(obj, lean)?;
        crate::types::LeanInt::ofNat(lean, nat)
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as u16;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (arbitrary precision natural number).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        unsafe {
            let val = Self::to_u16(obj);
            let ptr = ffi::inline::lean_uint16_to_nat(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint16_of_nat(nat.as_ptr());
            Self::mk(lean, val)
        }
    }

    /// Create from LeanNat with explicit truncation (same as ofNat).
    pub fn ofNatTruncate<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    /// Create from LeanNat with proof that value is less than size.
    /// In FFI context, this is the same as ofNat since we can't verify the proof.
    pub fn ofNatLT<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    // Comparison operations (non-decidable versions)

    /// Less than or equal comparison.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint16_dec_le(Self::to_u16(a), Self::to_u16(b)) }
    }

    /// Less than comparison.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint16_dec_lt(Self::to_u16(a), Self::to_u16(b)) }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_u16(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to LeanFloat32 (32-bit float).
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let val = lean_uint16_to_float32(Self::to_u16(obj));
            let ptr = ffi::inline::lean_box_float32(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // UInt conversions

    /// Convert to LeanUInt8.
    pub fn toUInt8<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt8>> {
        unsafe {
            let val = lean_uint16_to_uint8(Self::to_u16(obj));
            LeanUInt8::mk(lean, val)
        }
    }

    /// Convert to LeanUInt32.
    pub fn toUInt32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt32>> {
        unsafe {
            let val = lean_uint16_to_uint32(Self::to_u16(obj));
            LeanUInt32::mk(lean, val)
        }
    }

    /// Convert to LeanUInt64.
    pub fn toUInt64<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt64>> {
        unsafe {
            let val = lean_uint16_to_uint64(Self::to_u16(obj));
            LeanUInt64::mk(lean, val)
        }
    }

    /// Convert to LeanUSize.
    pub fn toUSize<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUSize>> {
        unsafe {
            let val = lean_uint16_to_usize(Self::to_u16(obj));
            LeanUSize::mk(lean, val)
        }
    }

    // Special operations

    /// Compute floor(log2(n)). Returns 0 for n = 0.
    pub fn log2<'l>(obj: &LeanBound<'l, Self>) -> u16 {
        let val = Self::to_u16(obj);
        if val == 0 {
            0
        } else {
            15 - val.leading_zeros() as u16
        }
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

#[allow(non_snake_case, missing_docs)]
impl LeanUInt32 {
    /// The number of distinct values: 2^32 = 4294967296.
    pub const SIZE: u64 = 4294967296;

    /// The minimum value: 0.
    pub const MIN: u32 = 0;

    /// The maximum value: 2^32 - 1 = 4294967295.
    pub const MAX: u32 = 4294967295;

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

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_add(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_sub(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_mul(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_div(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_mod(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_neg(Self::to_u32(a));
            Self::mk(lean, result)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_land(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_lor(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_xor(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_complement(Self::to_u32(a));
            Self::mk(lean, result)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_shift_left(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint32_shift_right(Self::to_u32(a), Self::to_u32(b));
            Self::mk(lean, result)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_dec_eq(Self::to_u32(a), Self::to_u32(b)) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_dec_lt(Self::to_u32(a), Self::to_u32(b)) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_dec_le(Self::to_u32(a), Self::to_u32(b)) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_is_valid_char(Self::to_u32(obj)) }
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_u32(obj);
        match char::from_u32(val) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        let nat = Self::toNat(obj, lean)?;
        crate::types::LeanInt::ofNat(lean, nat)
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as u32;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (arbitrary precision natural number).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        unsafe {
            let val = Self::to_u32(obj);
            let ptr = ffi::inline::lean_uint32_to_nat(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint32_of_nat(nat.as_ptr());
            Self::mk(lean, val)
        }
    }

    /// Create from LeanNat with explicit truncation (same as ofNat).
    pub fn ofNatTruncate<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    /// Create from LeanNat with proof that value is less than size.
    /// In FFI context, this is the same as ofNat since we can't verify the proof.
    pub fn ofNatLT<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    // Comparison operations (non-decidable versions)

    /// Less than or equal comparison.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_dec_le(Self::to_u32(a), Self::to_u32(b)) }
    }

    /// Less than comparison.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint32_dec_lt(Self::to_u32(a), Self::to_u32(b)) }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_u32(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to LeanFloat32 (32-bit float).
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let val = lean_uint32_to_float32(Self::to_u32(obj));
            let ptr = ffi::inline::lean_box_float32(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // UInt conversions

    /// Convert to LeanUInt8.
    pub fn toUInt8<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt8>> {
        unsafe {
            let val = lean_uint32_to_uint8(Self::to_u32(obj));
            LeanUInt8::mk(lean, val)
        }
    }

    /// Convert to LeanUInt16.
    pub fn toUInt16<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt16>> {
        unsafe {
            let val = lean_uint32_to_uint16(Self::to_u32(obj));
            LeanUInt16::mk(lean, val)
        }
    }

    /// Convert to LeanUInt64.
    pub fn toUInt64<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt64>> {
        unsafe {
            let val = lean_uint32_to_uint64(Self::to_u32(obj));
            LeanUInt64::mk(lean, val)
        }
    }

    /// Convert to LeanUSize.
    pub fn toUSize<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUSize>> {
        unsafe {
            let val = lean_uint32_to_usize(Self::to_u32(obj));
            LeanUSize::mk(lean, val)
        }
    }

    // Special operations

    /// Compute floor(log2(n)). Returns 0 for n = 0.
    pub fn log2<'l>(obj: &LeanBound<'l, Self>) -> u32 {
        let val = Self::to_u32(obj);
        if val == 0 {
            0
        } else {
            31 - val.leading_zeros()
        }
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

#[allow(non_snake_case, missing_docs)]
impl LeanUInt64 {
    /// The number of distinct values: 2^64.
    pub const SIZE: u128 = 18446744073709551616;

    /// The minimum value: 0.
    pub const MIN: u64 = 0;

    /// The maximum value: 2^64 - 1 = 18446744073709551615.
    pub const MAX: u64 = 18446744073709551615;

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

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_add(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_sub(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_mul(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_div(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_mod(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_neg(Self::to_u64(a));
            Self::mk(lean, result)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_land(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_lor(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_xor(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_complement(Self::to_u64(a));
            Self::mk(lean, result)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_shift_left(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_uint64_shift_right(Self::to_u64(a), Self::to_u64(b));
            Self::mk(lean, result)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint64_dec_eq(Self::to_u64(a), Self::to_u64(b)) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint64_dec_lt(Self::to_u64(a), Self::to_u64(b)) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint64_dec_le(Self::to_u64(a), Self::to_u64(b)) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_u64(obj);
        val < 0xD800 || (0xE000..=0x10FFFF).contains(&val)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_u64(obj);
        if val > u32::MAX as u64 {
            return Err(crate::err::LeanError::conversion(
                "Value out of range for Unicode scalar",
            ));
        }
        match char::from_u32(val as u32) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        let nat = Self::toNat(obj, lean)?;
        crate::types::LeanInt::ofNat(lean, nat)
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as u64;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (arbitrary precision natural number).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        unsafe {
            let val = Self::to_u64(obj);
            let ptr = ffi::inline::lean_uint64_to_nat(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_uint64_of_nat(nat.as_ptr());
            Self::mk(lean, val)
        }
    }

    /// Create from LeanNat with explicit truncation (same as ofNat).
    pub fn ofNatTruncate<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    /// Create from LeanNat with proof that value is less than size.
    /// In FFI context, this is the same as ofNat since we can't verify the proof.
    pub fn ofNatLT<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    // Comparison operations (non-decidable versions)

    /// Less than or equal comparison.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint64_dec_le(Self::to_u64(a), Self::to_u64(b)) }
    }

    /// Less than comparison.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_uint64_dec_lt(Self::to_u64(a), Self::to_u64(b)) }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_u64(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to LeanFloat32 (32-bit float).
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let val = lean_uint64_to_float32(Self::to_u64(obj));
            let ptr = ffi::inline::lean_box_float32(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // UInt conversions

    /// Convert to LeanUInt8.
    pub fn toUInt8<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt8>> {
        unsafe {
            let val = lean_uint64_to_uint8(Self::to_u64(obj));
            LeanUInt8::mk(lean, val)
        }
    }

    /// Convert to LeanUInt16.
    pub fn toUInt16<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt16>> {
        unsafe {
            let val = lean_uint64_to_uint16(Self::to_u64(obj));
            LeanUInt16::mk(lean, val)
        }
    }

    /// Convert to LeanUInt32.
    pub fn toUInt32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt32>> {
        unsafe {
            let val = lean_uint64_to_uint32(Self::to_u64(obj));
            LeanUInt32::mk(lean, val)
        }
    }

    /// Convert to LeanUSize.
    pub fn toUSize<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUSize>> {
        unsafe {
            let val = lean_uint64_to_usize(Self::to_u64(obj));
            LeanUSize::mk(lean, val)
        }
    }

    // Special operations

    /// Compute floor(log2(n)). Returns 0 for n = 0.
    pub fn log2<'l>(obj: &LeanBound<'l, Self>) -> u64 {
        let val = Self::to_u64(obj);
        if val == 0 {
            0
        } else {
            63 - val.leading_zeros() as u64
        }
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

#[allow(non_snake_case, missing_docs)]
impl LeanUSize {
    /// The number of distinct values (platform-dependent).
    #[cfg(target_pointer_width = "64")]
    pub const SIZE: u128 = 18446744073709551616; // 2^64

    #[cfg(target_pointer_width = "32")]
    pub const SIZE: u64 = 4294967296; // 2^32

    /// The minimum value: 0.
    pub const MIN: usize = 0;

    /// The maximum value (platform-dependent).
    #[cfg(target_pointer_width = "64")]
    pub const MAX: usize = 18446744073709551615; // 2^64 - 1

    #[cfg(target_pointer_width = "32")]
    pub const MAX: usize = 4294967295; // 2^32 - 1

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

    // Arithmetic operations

    pub fn add<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_add(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn sub<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_sub(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn mul<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_mul(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn div<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_div(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn mod_<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_mod(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn neg<'l>(lean: Lean<'l>, a: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_neg(Self::to_usize(a));
            Self::mk(lean, result)
        }
    }

    // Bitwise operations

    pub fn land<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_land(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn lor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_lor(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn xor<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_xor(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn complement<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_complement(Self::to_usize(a));
            Self::mk(lean, result)
        }
    }

    pub fn shiftLeft<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_shift_left(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    pub fn shiftRight<'l>(
        lean: Lean<'l>,
        a: &LeanBound<'l, Self>,
        b: &LeanBound<'l, Self>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let result = lean_usize_shift_right(Self::to_usize(a), Self::to_usize(b));
            Self::mk(lean, result)
        }
    }

    // Comparison operations

    pub fn decEq<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_usize_dec_eq(Self::to_usize(a), Self::to_usize(b)) }
    }

    pub fn decLt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_usize_dec_lt(Self::to_usize(a), Self::to_usize(b)) }
    }

    pub fn decLe<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_usize_dec_le(Self::to_usize(a), Self::to_usize(b)) }
    }

    // Character operations

    pub fn isValidChar<'l>(obj: &LeanBound<'l, Self>) -> bool {
        let val = Self::to_usize(obj) as u64;
        val < 0xD800 || (0xE000..=0x10FFFF).contains(&val)
    }

    pub fn toChar<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanChar>> {
        let val = Self::to_usize(obj) as u64;
        if val > u32::MAX as u64 {
            return Err(crate::err::LeanError::conversion(
                "Value out of range for Unicode scalar",
            ));
        }
        match char::from_u32(val as u32) {
            Some(c) => LeanChar::mk(lean, c),
            None => Err(crate::err::LeanError::conversion(
                "Invalid Unicode scalar value",
            )),
        }
    }

    // Conversions to/from arbitrary precision types

    /// Convert to LeanInt (arbitrary precision integer).
    pub fn toInt<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanInt>> {
        let nat = Self::toNat(obj, lean)?;
        crate::types::LeanInt::ofNat(lean, nat)
    }

    /// Create from LeanInt (wrapping if out of range).
    pub fn ofInt<'l>(
        lean: Lean<'l>,
        int: &LeanBound<'l, crate::types::LeanInt>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        let val = crate::types::LeanInt::to_i64(int).unwrap_or(0) as usize;
        Self::mk(lean, val)
    }

    /// Convert to LeanNat (arbitrary precision natural number).
    pub fn toNat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanNat>> {
        unsafe {
            let val = Self::to_usize(obj);
            let ptr = ffi::inline::lean_usize_to_nat(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create from LeanNat (wrapping if out of range).
    pub fn ofNat<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let val = ffi::inline::lean_usize_of_nat(nat.as_ptr());
            Self::mk(lean, val)
        }
    }

    /// Create from LeanNat with explicit truncation (same as ofNat).
    pub fn ofNatTruncate<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    /// Create from LeanNat with proof that value is less than size.
    /// In FFI context, this is the same as ofNat since we can't verify the proof.
    pub fn ofNatLT<'l>(
        lean: Lean<'l>,
        nat: &LeanBound<'l, crate::types::LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        Self::ofNat(lean, nat)
    }

    // Comparison operations (non-decidable versions)

    /// Less than or equal comparison.
    pub fn le<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_usize_dec_le(Self::to_usize(a), Self::to_usize(b)) }
    }

    /// Less than comparison.
    pub fn lt<'l>(a: &LeanBound<'l, Self>, b: &LeanBound<'l, Self>) -> bool {
        unsafe { lean_usize_dec_lt(Self::to_usize(a), Self::to_usize(b)) }
    }

    // Float conversions

    /// Convert to LeanFloat (64-bit float).
    pub fn toFloat<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat>> {
        unsafe {
            let val = Self::to_usize(obj) as f64;
            let ptr = ffi::inline::lean_box_float(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Convert to LeanFloat32 (32-bit float).
    pub fn toFloat32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, crate::types::LeanFloat32>> {
        unsafe {
            let val = lean_usize_to_float32(Self::to_usize(obj));
            let ptr = ffi::inline::lean_box_float32(val);
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    // UInt conversions

    /// Convert to LeanUInt8.
    pub fn toUInt8<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt8>> {
        unsafe {
            let val = lean_usize_to_uint8(Self::to_usize(obj));
            LeanUInt8::mk(lean, val)
        }
    }

    /// Convert to LeanUInt16.
    pub fn toUInt16<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt16>> {
        unsafe {
            let val = lean_usize_to_uint16(Self::to_usize(obj));
            LeanUInt16::mk(lean, val)
        }
    }

    /// Convert to LeanUInt32.
    pub fn toUInt32<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt32>> {
        unsafe {
            let val = lean_usize_to_uint32(Self::to_usize(obj));
            LeanUInt32::mk(lean, val)
        }
    }

    /// Convert to LeanUInt64.
    pub fn toUInt64<'l>(
        obj: &LeanBound<'l, Self>,
        lean: Lean<'l>,
    ) -> LeanResult<LeanBound<'l, LeanUInt64>> {
        unsafe {
            let val = lean_usize_to_uint64(Self::to_usize(obj));
            LeanUInt64::mk(lean, val)
        }
    }

    // Special operations

    /// Compute floor(log2(n)). Returns 0 for n = 0.
    pub fn log2<'l>(obj: &LeanBound<'l, Self>) -> usize {
        let val = Self::to_usize(obj);
        if val == 0 {
            0
        } else {
            (std::mem::size_of::<usize>() * 8 - 1) - val.leading_zeros() as usize
        }
    }
}

impl<'l> std::fmt::Debug for LeanBound<'l, LeanUSize> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanUSize({})", LeanUSize::to_usize(self))
    }
}
