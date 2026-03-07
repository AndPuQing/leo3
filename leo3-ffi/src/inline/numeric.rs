//! Numeric inline helpers copied from Lean's static inline API surface.

use super::{
    likely,
    nat::{lean_nat_succ, lean_usize_to_nat, LEAN_MAX_SMALL_NAT},
    object::{
        lean_box, lean_ctor_get_float, lean_ctor_get_float32, lean_ctor_set_float,
        lean_ctor_set_float32, lean_dec, lean_is_scalar, lean_unbox,
    },
};
use crate::object::{b_lean_obj_arg, lean_obj_arg, lean_obj_res, lean_object};
use libc::c_uint;
use libc::size_t;

// Integer Functions
// ============================================================================

// Import the big int functions from the int module
use crate::int::{
    lean_big_int64_to_int, lean_big_size_t_to_int, lean_int_big_add, lean_int_big_div,
    lean_int_big_ediv, lean_int_big_emod, lean_int_big_eq, lean_int_big_le, lean_int_big_lt,
    lean_int_big_mod, lean_int_big_mul, lean_int_big_neg, lean_int_big_sub,
};

// Constants for small int range
const LEAN_MAX_SMALL_INT: i64 = if std::mem::size_of::<*const ()>() == 8 {
    i32::MAX as i64
} else {
    (i32::MAX >> 1) as i64
};

const LEAN_MIN_SMALL_INT: i64 = if std::mem::size_of::<*const ()>() == 8 {
    i32::MIN as i64
} else {
    (i32::MIN >> 1) as i64
};

/// Convert i64 to Lean Int.
///
/// For small integers (within LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT),
/// boxes them directly. For large integers, allocates a big int object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_int64_to_int(n: i64) -> lean_obj_res {
    if likely((LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT).contains(&n)) {
        lean_box(n as usize)
    } else {
        lean_big_int64_to_int(n)
    }
}

/// Convert scalar Int to i64.
///
/// # Safety
/// - `a` must be a scalar Int
#[inline]
pub unsafe fn lean_scalar_to_int64(a: b_lean_obj_arg) -> i64 {
    debug_assert!(lean_is_scalar(a));
    if std::mem::size_of::<*const ()>() == 8 {
        lean_unbox(a) as i32 as i64
    } else {
        ((a as isize) >> 1) as i64
    }
}

/// Convert scalar Int to i32.
///
/// # Safety
/// - `a` must be a scalar Int
#[inline]
pub unsafe fn lean_scalar_to_int(a: b_lean_obj_arg) -> i32 {
    debug_assert!(lean_is_scalar(a));
    if std::mem::size_of::<*const ()>() == 8 {
        lean_unbox(a) as i32
    } else {
        ((a as isize) >> 1) as i32
    }
}

/// Convert a Lean Nat to a Lean Int.
///
/// This is the runtime implementation of `Int.ofNat`.
/// For small nats that fit in the small int range, returns the same pointer.
/// For larger values, converts to appropriate int representation.
///
/// # Safety
/// - `a` must be a valid Nat object (consumed)
#[inline]
pub unsafe fn lean_nat_to_int(a: lean_obj_arg) -> lean_obj_res {
    if lean_is_scalar(a) {
        let v = lean_unbox(a);
        if v <= LEAN_MAX_SMALL_INT as usize {
            // Small nat that fits in small int range - return as-is
            a
        } else {
            // Nat is scalar but too large for small int - convert to big int
            lean_big_size_t_to_int(v)
        }
    } else {
        // Big nat - return as-is (big nat and big positive int have same representation)
        a
    }
}

/// Negate an integer.
///
/// # Safety
/// - `a` must be a valid Int object
#[inline]
pub unsafe fn lean_int_neg(a: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a)) {
        lean_int64_to_int(-lean_scalar_to_int64(a))
    } else {
        lean_int_big_neg(a)
    }
}

/// Create negative integer from successor of nat (inline from lean.h)
///
/// # Safety
/// - `a` must be a valid nat object (consumed)
#[inline]
pub unsafe fn lean_int_neg_succ_of_nat(a: lean_obj_arg) -> lean_obj_res {
    let s = lean_nat_succ(a);
    lean_dec(a);
    let i = lean_nat_to_int(s);
    let r = lean_int_neg(i);
    lean_dec(i);
    r
}

/// Integer decidable equality (inline from lean.h)
///
/// # Safety
/// - `a1` and `a2` must be valid int objects
#[inline(always)]
pub unsafe fn lean_int_dec_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    lean_int_eq(a1, a2)
}

/// Add two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_add(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2))
    } else {
        lean_int_big_add(a1, a2)
    }
}

/// Subtract two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_sub(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2))
    } else {
        lean_int_big_sub(a1, a2)
    }
}

/// Multiply two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_mul(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2))
    } else {
        lean_int_big_mul(a1, a2)
    }
}

/// Divide two integers (truncated division).
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns 0 if dividing by zero
#[inline]
pub unsafe fn lean_int_div(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let v1 = lean_scalar_to_int(a1) as i64;
            let v2 = lean_scalar_to_int(a2) as i64;
            if v2 == 0 {
                lean_box(0)
            } else {
                lean_int64_to_int(v1 / v2)
            }
        } else {
            let v1 = lean_scalar_to_int(a1);
            let v2 = lean_scalar_to_int(a2);
            if v2 == 0 {
                lean_box(0)
            } else {
                lean_int64_to_int((v1 / v2) as i64)
            }
        }
    } else {
        lean_int_big_div(a1, a2)
    }
}

/// Modulus of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns a1 if dividing by zero
#[inline]
pub unsafe fn lean_int_mod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let v1 = lean_scalar_to_int64(a1);
            let v2 = lean_scalar_to_int64(a2);
            if v2 == 0 {
                a1 as lean_obj_res
            } else {
                lean_int64_to_int(v1 % v2)
            }
        } else {
            let v1 = lean_scalar_to_int(a1);
            let v2 = lean_scalar_to_int(a2);
            if v2 == 0 {
                a1 as lean_obj_res
            } else {
                lean_int64_to_int((v1 % v2) as i64)
            }
        }
    } else {
        lean_int_big_mod(a1, a2)
    }
}

/// Euclidean division of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns 0 if dividing by zero
#[inline]
pub unsafe fn lean_int_ediv(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let n = lean_scalar_to_int(a1) as i64;
            let d = lean_scalar_to_int(a2) as i64;
            if d == 0 {
                lean_box(0)
            } else {
                let q = n / d;
                let r = n % d;
                if (r > 0 && d < 0) || (r < 0 && d > 0) {
                    lean_int64_to_int(q - 1)
                } else {
                    lean_int64_to_int(q)
                }
            }
        } else {
            let n = lean_scalar_to_int(a1);
            let d = lean_scalar_to_int(a2);
            if d == 0 {
                lean_box(0)
            } else {
                let q = n / d;
                let r = n % d;
                if (r > 0 && d < 0) || (r < 0 && d > 0) {
                    lean_int64_to_int((q - 1) as i64)
                } else {
                    lean_int64_to_int(q as i64)
                }
            }
        }
    } else {
        lean_int_big_ediv(a1, a2)
    }
}

/// Euclidean modulus of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
/// - Returns a1 if dividing by zero
#[inline]
pub unsafe fn lean_int_emod(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> lean_obj_res {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        if std::mem::size_of::<*const ()>() == 8 {
            let n = lean_scalar_to_int64(a1);
            let d = lean_scalar_to_int64(a2);
            if d == 0 {
                a1 as lean_obj_res
            } else {
                let r = n % d;
                if r < 0 {
                    if d > 0 {
                        lean_int64_to_int(r + d)
                    } else {
                        lean_int64_to_int(r - d)
                    }
                } else if r == 0 {
                    lean_box(0)
                } else if d < 0 {
                    lean_int64_to_int(r + d)
                } else {
                    lean_int64_to_int(r)
                }
            }
        } else {
            let n = lean_scalar_to_int(a1) as i64;
            let d = lean_scalar_to_int(a2) as i64;
            if d == 0 {
                a1 as lean_obj_res
            } else {
                let r = n % d;
                if r < 0 {
                    if d > 0 {
                        lean_int64_to_int(r + d)
                    } else {
                        lean_int64_to_int(r - d)
                    }
                } else if r == 0 {
                    lean_box(0)
                } else if d < 0 {
                    lean_int64_to_int(r + d)
                } else {
                    lean_int64_to_int(r)
                }
            }
        }
    } else {
        lean_int_big_emod(a1, a2)
    }
}

/// Check equality of two integers.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_eq(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        a1 == a2
    } else {
        lean_int_big_eq(a1, a2)
    }
}

/// Check if first integer is less than or equal to second.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_le(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_scalar_to_int(a1) <= lean_scalar_to_int(a2)
    } else {
        lean_int_big_le(a1, a2)
    }
}

/// Check if first integer is less than second.
///
/// # Safety
/// - `a1` and `a2` must be valid Int objects
#[inline]
pub unsafe fn lean_int_lt(a1: b_lean_obj_arg, a2: b_lean_obj_arg) -> bool {
    if likely(lean_is_scalar(a1) && lean_is_scalar(a2)) {
        lean_scalar_to_int(a1) < lean_scalar_to_int(a2)
    } else {
        lean_int_big_lt(a1, a2)
    }
}

// ============================================================================
// Float Functions
// ============================================================================

/// Box a double into a Lean Float object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_box_float(v: f64) -> lean_obj_res {
    let o = crate::lean_alloc_ctor(0, 0, std::mem::size_of::<f64>() as c_uint);
    lean_ctor_set_float(o, 0, v);
    o
}

/// Unbox a Lean Float object to a double.
///
/// # Safety
/// - `o` must be a valid Float object
#[inline]
pub unsafe fn lean_unbox_float(o: b_lean_obj_arg) -> f64 {
    lean_ctor_get_float(o, 0)
}

/// Box a float (f32) into a Lean Float32 object.
///
/// # Safety
/// - Always safe to call
#[inline]
pub unsafe fn lean_box_float32(v: f32) -> lean_obj_res {
    let o = crate::lean_alloc_ctor(0, 0, std::mem::size_of::<f32>() as c_uint);
    lean_ctor_set_float32(o, 0, v);
    o
}

/// Unbox a Lean Float32 object to a float.
///
/// # Safety
/// - `o` must be a valid Float32 object
#[inline]
pub unsafe fn lean_unbox_float32(o: b_lean_obj_arg) -> f32 {
    lean_ctor_get_float32(o, 0)
}

#[inline]
pub unsafe fn lean_float32_to_uint8(a: f32) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_float32_to_uint16(a: f32) -> u16 {
    a as u16
}

/// Convert Float32 to UInt32
#[inline]
pub unsafe fn lean_float32_to_uint32(a: f32) -> u32 {
    a as u32
}

/// Convert Float32 to UInt64
#[inline]
pub unsafe fn lean_float32_to_uint64(a: f32) -> u64 {
    a as u64
}

/// Convert Float32 to USize
#[inline]
pub unsafe fn lean_float32_to_usize(a: f32) -> usize {
    a as usize
}

/// Convert Float32 to Int8
#[inline]
pub unsafe fn lean_float32_to_int8(a: f32) -> i8 {
    a as i8
}

/// Convert Float32 to Int16
#[inline]
pub unsafe fn lean_float32_to_int16(a: f32) -> i16 {
    a as i16
}

/// Convert Float32 to Int32
#[inline]
pub unsafe fn lean_float32_to_int32(a: f32) -> i32 {
    a as i32
}

/// Convert Float32 to Int64
#[inline]
pub unsafe fn lean_float32_to_int64(a: f32) -> i64 {
    a as i64
}

/// Convert Float32 to ISize
#[inline]
pub unsafe fn lean_float32_to_isize(a: f32) -> isize {
    a as isize
}

/// Convert UInt8 to Float32
#[inline]
pub unsafe fn lean_uint8_to_float32(a: u8) -> f32 {
    a as f32
}

/// Convert UInt16 to Float32
#[inline]
pub unsafe fn lean_uint16_to_float32(a: u16) -> f32 {
    a as f32
}

/// Convert UInt32 to Float32
#[inline]
pub unsafe fn lean_uint32_to_float32(a: u32) -> f32 {
    a as f32
}

/// Convert UInt64 to Float32
#[inline]
pub unsafe fn lean_uint64_to_float32(a: u64) -> f32 {
    a as f32
}

/// Convert USize to Float32
#[inline]
pub fn lean_usize_to_float32(a: usize) -> f32 {
    a as f32
}

/// Convert Int8 to Float32
#[inline]
pub unsafe fn lean_int8_to_float32(a: i8) -> f32 {
    a as f32
}

/// Convert Int16 to Float32
#[inline]
pub unsafe fn lean_int16_to_float32(a: i16) -> f32 {
    a as f32
}

/// Convert Int32 to Float32
#[inline]
pub unsafe fn lean_int32_to_float32(a: i32) -> f32 {
    a as f32
}

/// Convert Int64 to Float32
#[inline]
pub unsafe fn lean_int64_to_float32(a: i64) -> f32 {
    a as f32
}

/// Convert ISize to Float32
#[inline]
pub unsafe fn lean_isize_to_float32(a: isize) -> f32 {
    a as f32
}

/// Convert Float to Float32
#[inline]
pub unsafe fn lean_float_to_float32(a: f64) -> f32 {
    a as f32
}

/// Convert Float32 to Float
#[inline]
pub unsafe fn lean_float32_to_float(a: f32) -> f64 {
    a as f64
}

/// Convert Float to UInt8
#[inline]
pub unsafe fn lean_float_to_uint8(a: f64) -> u8 {
    a as u8
}

/// Convert Float to UInt16
#[inline]
pub unsafe fn lean_float_to_uint16(a: f64) -> u16 {
    a as u16
}

/// Convert Float to UInt32
#[inline]
pub unsafe fn lean_float_to_uint32(a: f64) -> u32 {
    a as u32
}

/// Convert Float to UInt64
#[inline]
pub unsafe fn lean_float_to_uint64(a: f64) -> u64 {
    a as u64
}

/// Convert Float to USize
#[inline]
pub unsafe fn lean_float_to_usize(a: f64) -> usize {
    a as usize
}

/// Convert Float to Int8
#[inline]
pub unsafe fn lean_float_to_int8(a: f64) -> i8 {
    a as i8
}

/// Convert Float to Int16
#[inline]
pub unsafe fn lean_float_to_int16(a: f64) -> i16 {
    a as i16
}

/// Convert Float to Int32
#[inline]
pub unsafe fn lean_float_to_int32(a: f64) -> i32 {
    a as i32
}

/// Convert Float to Int64
#[inline]
pub unsafe fn lean_float_to_int64(a: f64) -> i64 {
    a as i64
}

/// Convert Float to ISize
#[inline]
pub unsafe fn lean_float_to_isize(a: f64) -> isize {
    a as isize
}

/// Convert UInt8 to Float
#[inline]
pub unsafe fn lean_uint8_to_float(a: u8) -> f64 {
    a as f64
}

/// Convert UInt16 to Float
#[inline]
pub unsafe fn lean_uint16_to_float(a: u16) -> f64 {
    a as f64
}

/// Convert UInt32 to Float
#[inline]
pub unsafe fn lean_uint32_to_float(a: u32) -> f64 {
    a as f64
}

/// Convert UInt64 to Float
#[inline]
pub unsafe fn lean_uint64_to_float(a: u64) -> f64 {
    a as f64
}

/// Convert USize to Float
#[inline]
pub unsafe fn lean_usize_to_float(a: usize) -> f64 {
    a as f64
}

/// Convert Int8 to Float
#[inline]
pub unsafe fn lean_int8_to_float(a: i8) -> f64 {
    a as f64
}

/// Convert Int16 to Float
#[inline]
pub unsafe fn lean_int16_to_float(a: i16) -> f64 {
    a as f64
}

/// Convert Int32 to Float
#[inline]
pub unsafe fn lean_int32_to_float(a: i32) -> f64 {
    a as f64
}

/// Convert Int64 to Float
#[inline]
pub unsafe fn lean_int64_to_float(a: i64) -> f64 {
    a as f64
}

/// Convert ISize to Float
#[inline]
pub unsafe fn lean_isize_to_float(a: isize) -> f64 {
    a as f64
}

// UInt8 conversions
#[inline]
pub unsafe fn lean_uint8_to_uint16(a: u8) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint8_to_uint32(a: u8) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint8_to_uint64(a: u8) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint8_to_usize(a: u8) -> usize {
    a as usize
}

// UInt16 conversions
#[inline]
pub unsafe fn lean_uint16_to_uint8(a: u16) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint16_to_uint32(a: u16) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint16_to_uint64(a: u16) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint16_to_usize(a: u16) -> usize {
    a as usize
}

// UInt32 conversions
#[inline]
pub unsafe fn lean_uint32_to_uint8(a: u32) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint32_to_uint16(a: u32) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint32_to_uint64(a: u32) -> u64 {
    a as u64
}

#[inline]
pub unsafe fn lean_uint32_to_usize(a: u32) -> usize {
    a as usize
}

// UInt64 conversions
#[inline]
pub unsafe fn lean_uint64_to_uint8(a: u64) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_uint64_to_uint16(a: u64) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_uint64_to_uint32(a: u64) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_uint64_to_usize(a: u64) -> usize {
    a as usize
}

// USize conversions
#[inline]
pub unsafe fn lean_usize_to_uint8(a: usize) -> u8 {
    a as u8
}

#[inline]
pub unsafe fn lean_usize_to_uint16(a: usize) -> u16 {
    a as u16
}

#[inline]
pub unsafe fn lean_usize_to_uint32(a: usize) -> u32 {
    a as u32
}

#[inline]
pub unsafe fn lean_usize_to_uint64(a: usize) -> u64 {
    a as u64
}

// Int8 conversions
#[inline]
pub unsafe fn lean_int8_to_int16(a: u8) -> u16 {
    (a as i8 as i16) as u16
}

#[inline]
pub unsafe fn lean_int8_to_int32(a: u8) -> u32 {
    (a as i8 as i32) as u32
}

#[inline]
pub unsafe fn lean_int8_to_int64(a: u8) -> u64 {
    (a as i8 as i64) as u64
}

#[inline]
pub unsafe fn lean_int8_to_isize(a: u8) -> usize {
    (a as i8 as isize) as usize
}

// Int16 conversions
#[inline]
pub unsafe fn lean_int16_to_int8(a: u16) -> u8 {
    (a as i16 as i8) as u8
}

#[inline]
pub unsafe fn lean_int16_to_int32(a: u16) -> u32 {
    (a as i16 as i32) as u32
}

#[inline]
pub unsafe fn lean_int16_to_int64(a: u16) -> u64 {
    (a as i16 as i64) as u64
}

#[inline]
pub unsafe fn lean_int16_to_isize(a: u16) -> usize {
    (a as i16 as isize) as usize
}

// Int32 conversions
#[inline]
pub unsafe fn lean_int32_to_int8(a: u32) -> u8 {
    (a as i32 as i8) as u8
}

#[inline]
pub unsafe fn lean_int32_to_int16(a: u32) -> u16 {
    (a as i32 as i16) as u16
}

#[inline]
pub unsafe fn lean_int32_to_int64(a: u32) -> u64 {
    (a as i32 as i64) as u64
}

#[inline]
pub unsafe fn lean_int32_to_isize(a: u32) -> usize {
    (a as i32 as isize) as usize
}

// Int64 conversions
#[inline]
pub unsafe fn lean_int64_to_int8(a: u64) -> u8 {
    (a as i64 as i8) as u8
}

#[inline]
pub unsafe fn lean_int64_to_int16(a: u64) -> u16 {
    (a as i64 as i16) as u16
}

#[inline]
pub unsafe fn lean_int64_to_int32(a: u64) -> u32 {
    (a as i64 as i32) as u32
}

#[inline]
pub unsafe fn lean_int64_to_isize(a: u64) -> usize {
    (a as i64 as isize) as usize
}

// ISize conversions
#[inline]
pub unsafe fn lean_isize_to_int8(a: usize) -> u8 {
    (a as isize as i8) as u8
}

#[inline]
pub unsafe fn lean_isize_to_int16(a: usize) -> u16 {
    (a as isize as i16) as u16
}

#[inline]
pub unsafe fn lean_isize_to_int32(a: usize) -> u32 {
    (a as isize as i32) as u32
}

#[inline]
pub unsafe fn lean_isize_to_int64(a: usize) -> u64 {
    (a as isize as i64) as u64
}

/// Add two Float values
#[inline]
pub unsafe fn lean_float_add(a: f64, b: f64) -> f64 {
    a + b
}

/// Subtract two Float values
#[inline]
pub unsafe fn lean_float_sub(a: f64, b: f64) -> f64 {
    a - b
}

/// Multiply two Float values
#[inline]
pub unsafe fn lean_float_mul(a: f64, b: f64) -> f64 {
    a * b
}

/// Divide two Float values
#[inline]
pub unsafe fn lean_float_div(a: f64, b: f64) -> f64 {
    a / b
}

/// Negate a Float value
#[inline]
pub unsafe fn lean_float_negate(a: f64) -> f64 {
    -a
}

// ============================================================================
// Float comparison operations (static inline from lean.h)
// ============================================================================

/// Float equality comparison
#[inline]
pub unsafe fn lean_float_beq(a: f64, b: f64) -> u8 {
    (a == b) as u8
}

/// Float decidable less than or equal comparison
#[inline]
pub unsafe fn lean_float_decLe(a: f64, b: f64) -> u8 {
    (a <= b) as u8
}

/// Float decidable less than comparison
#[inline]
pub unsafe fn lean_float_decLt(a: f64, b: f64) -> u8 {
    (a < b) as u8
}

/// Add two Float32 values
#[inline]
pub unsafe fn lean_float32_add(a: f32, b: f32) -> f32 {
    a + b
}

/// Subtract two Float32 values
#[inline]
pub unsafe fn lean_float32_sub(a: f32, b: f32) -> f32 {
    a - b
}

/// Multiply two Float32 values
#[inline]
pub unsafe fn lean_float32_mul(a: f32, b: f32) -> f32 {
    a * b
}

/// Divide two Float32 values
#[inline]
pub unsafe fn lean_float32_div(a: f32, b: f32) -> f32 {
    a / b
}

/// Negate a Float32 value
#[inline]
pub unsafe fn lean_float32_negate(a: f32) -> f32 {
    -a
}

/// Float32 equality comparison
#[inline]
pub unsafe fn lean_float32_beq(a: f32, b: f32) -> u8 {
    (a == b) as u8
}

/// Float32 decidable less than or equal comparison
#[inline]
pub unsafe fn lean_float32_decLe(a: f32, b: f32) -> u8 {
    (a <= b) as u8
}

/// Float32 decidable less than comparison
#[inline]
pub unsafe fn lean_float32_decLt(a: f32, b: f32) -> u8 {
    (a < b) as u8
}

// --- UInt8 Operations ---

#[inline(always)]
pub unsafe fn lean_uint8_add(a1: u8, a2: u8) -> u8 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_sub(a1: u8, a2: u8) -> u8 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_mul(a1: u8, a2: u8) -> u8 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint8_div(a1: u8, a2: u8) -> u8 {
    a1.checked_div(a2).unwrap_or(0)
}

#[inline(always)]
pub unsafe fn lean_uint8_mod(a1: u8, a2: u8) -> u8 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint8_land(a1: u8, a2: u8) -> u8 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint8_lor(a1: u8, a2: u8) -> u8 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint8_xor(a1: u8, a2: u8) -> u8 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint8_complement(a: u8) -> u8 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint8_shift_left(a1: u8, a2: u8) -> u8 {
    a1.wrapping_shl((a2 % 8) as u32)
}

#[inline(always)]
pub unsafe fn lean_uint8_shift_right(a1: u8, a2: u8) -> u8 {
    a1 >> (a2 % 8)
}

#[inline(always)]
pub unsafe fn lean_uint8_neg(a: u8) -> u8 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_eq(a1: u8, a2: u8) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_lt(a1: u8, a2: u8) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint8_dec_le(a1: u8, a2: u8) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint8_log2(a: u8) -> u8 {
    if a == 0 {
        0
    } else {
        7 - a.leading_zeros() as u8
    }
}

// --- UInt16 Operations ---

#[inline(always)]
pub unsafe fn lean_uint16_add(a1: u16, a2: u16) -> u16 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_sub(a1: u16, a2: u16) -> u16 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_mul(a1: u16, a2: u16) -> u16 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint16_div(a1: u16, a2: u16) -> u16 {
    a1.checked_div(a2).unwrap_or(0)
}

#[inline(always)]
pub unsafe fn lean_uint16_mod(a1: u16, a2: u16) -> u16 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint16_land(a1: u16, a2: u16) -> u16 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint16_lor(a1: u16, a2: u16) -> u16 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint16_xor(a1: u16, a2: u16) -> u16 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint16_complement(a: u16) -> u16 {
    !a
}
#[inline(always)]
pub unsafe fn lean_uint16_shift_left(a1: u16, a2: u16) -> u16 {
    let shift = (a2 & 0xF) as u32;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint16_shift_right(a1: u16, a2: u16) -> u16 {
    let shift = (a2 & 0xF) as u32;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint16_neg(a: u16) -> u16 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_eq(a1: u16, a2: u16) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_lt(a1: u16, a2: u16) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint16_dec_le(a1: u16, a2: u16) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint16_log2(a: u16) -> u16 {
    if a == 0 {
        0
    } else {
        15 - a.leading_zeros() as u16
    }
}

// --- UInt32 Operations ---

#[inline(always)]
pub unsafe fn lean_uint32_add(a1: u32, a2: u32) -> u32 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_sub(a1: u32, a2: u32) -> u32 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_mul(a1: u32, a2: u32) -> u32 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint32_div(a1: u32, a2: u32) -> u32 {
    a1.checked_div(a2).unwrap_or(0)
}

#[inline(always)]
pub unsafe fn lean_uint32_mod(a1: u32, a2: u32) -> u32 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint32_land(a1: u32, a2: u32) -> u32 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint32_lor(a1: u32, a2: u32) -> u32 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint32_xor(a1: u32, a2: u32) -> u32 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint32_complement(a: u32) -> u32 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint32_shift_left(a1: u32, a2: u32) -> u32 {
    let shift = a2 & 31;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint32_shift_right(a1: u32, a2: u32) -> u32 {
    let shift = a2 & 31;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint32_neg(a: u32) -> u32 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_eq(a1: u32, a2: u32) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_lt(a1: u32, a2: u32) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint32_dec_le(a1: u32, a2: u32) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint32_is_valid_char(a: u32) -> bool {
    (a < 0xD800) || (0xE000..=0x10FFFF).contains(&a)
}

#[inline(always)]
pub unsafe fn lean_uint32_log2(a: u32) -> u32 {
    if a == 0 {
        0
    } else {
        31 - a.leading_zeros()
    }
}

// --- UInt64 Operations ---

#[inline(always)]
pub unsafe fn lean_uint64_add(a1: u64, a2: u64) -> u64 {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_sub(a1: u64, a2: u64) -> u64 {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_mul(a1: u64, a2: u64) -> u64 {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_uint64_div(a1: u64, a2: u64) -> u64 {
    a1.checked_div(a2).unwrap_or(0)
}

#[inline(always)]
pub unsafe fn lean_uint64_mod(a1: u64, a2: u64) -> u64 {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_land(a1: u64, a2: u64) -> u64 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_uint64_lor(a1: u64, a2: u64) -> u64 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_uint64_xor(a1: u64, a2: u64) -> u64 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_uint64_complement(a: u64) -> u64 {
    !a
}

#[inline(always)]
pub unsafe fn lean_uint64_shift_left(a1: u64, a2: u64) -> u64 {
    let shift = (a2 & 63) as u32; // smod 64
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_uint64_shift_right(a1: u64, a2: u64) -> u64 {
    let shift = (a2 & 63) as u32; // smod 64
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_uint64_neg(a: u64) -> u64 {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_eq(a1: u64, a2: u64) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_lt(a1: u64, a2: u64) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_uint64_dec_le(a1: u64, a2: u64) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_uint64_log2(a: u64) -> u64 {
    if a == 0 {
        0
    } else {
        63 - a.leading_zeros() as u64
    }
}

// --- Conversion Functions: UInt to/from Nat ---

#[inline(always)]
pub unsafe fn lean_uint8_to_nat(a: u8) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint8_of_nat(a: *const lean_object) -> u8 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u8
    } else {
        crate::nat::lean_uint8_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint16_to_nat(a: u16) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint16_of_nat(a: *const lean_object) -> u16 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u16
    } else {
        crate::nat::lean_uint16_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint32_to_nat(a: u32) -> *mut lean_object {
    lean_usize_to_nat(a as usize)
}

#[inline(always)]
pub unsafe fn lean_uint32_of_nat(a: *const lean_object) -> u32 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u32
    } else {
        crate::nat::lean_uint32_of_big_nat(a)
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_to_nat(n: u64) -> *mut lean_object {
    if n <= LEAN_MAX_SMALL_NAT as u64 {
        lean_box(n as usize)
    } else {
        crate::nat::lean_big_uint64_to_nat(n)
    }
}

#[inline(always)]
pub unsafe fn lean_uint64_of_nat(a: *const lean_object) -> u64 {
    if lean_is_scalar(a) {
        lean_unbox(a) as u64
    } else {
        crate::nat::lean_uint64_of_big_nat(a)
    }
}

// --- USize Operations ---

#[inline(always)]
pub unsafe fn lean_usize_add(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_add(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_sub(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_sub(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_mul(a1: size_t, a2: size_t) -> size_t {
    a1.wrapping_mul(a2)
}

#[inline(always)]
pub unsafe fn lean_usize_div(a1: size_t, a2: size_t) -> size_t {
    a1.checked_div(a2).unwrap_or(0)
}

#[inline(always)]
pub unsafe fn lean_usize_mod(a1: size_t, a2: size_t) -> size_t {
    if a2 == 0 {
        a1
    } else {
        a1 % a2
    }
}

#[inline(always)]
pub unsafe fn lean_usize_land(a1: size_t, a2: size_t) -> size_t {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_usize_lor(a1: size_t, a2: size_t) -> size_t {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_usize_xor(a1: size_t, a2: size_t) -> size_t {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_usize_complement(a: size_t) -> size_t {
    !a
}

#[inline(always)]
pub unsafe fn lean_usize_shift_left(a1: size_t, a2: size_t) -> size_t {
    #[cfg(target_pointer_width = "64")]
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32;
    #[cfg(target_pointer_width = "32")]
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32;
    a1.wrapping_shl(shift)
}

#[inline(always)]
pub unsafe fn lean_usize_shift_right(a1: size_t, a2: size_t) -> size_t {
    #[cfg(target_pointer_width = "64")]
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32;
    #[cfg(target_pointer_width = "32")]
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32;
    a1.wrapping_shr(shift)
}

#[inline(always)]
pub unsafe fn lean_usize_neg(a: size_t) -> size_t {
    a.wrapping_neg()
}

#[inline(always)]
pub unsafe fn lean_usize_dec_eq(a1: size_t, a2: size_t) -> bool {
    a1 == a2
}

#[inline(always)]
pub unsafe fn lean_usize_dec_lt(a1: size_t, a2: size_t) -> bool {
    a1 < a2
}

#[inline(always)]
pub unsafe fn lean_usize_dec_le(a1: size_t, a2: size_t) -> bool {
    a1 <= a2
}

#[inline(always)]
pub unsafe fn lean_usize_log2(a: size_t) -> size_t {
    if a == 0 {
        0
    } else {
        (std::mem::size_of::<usize>() * 8 - 1) - a.leading_zeros() as usize
    }
}

#[inline(always)]
pub unsafe fn lean_int8_add(a1: u8, a2: u8) -> u8 {
    (a1 as i8).wrapping_add(a2 as i8) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_sub(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (lhs.wrapping_sub(rhs)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_mul(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (lhs.wrapping_mul(rhs)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_div(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_mod(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let rhs = a2 as i8;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_land(a1: u8, a2: u8) -> u8 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int8_lor(a1: u8, a2: u8) -> u8 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int8_xor(a1: u8, a2: u8) -> u8 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int8_complement(a: u8) -> u8 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int8_shift_left(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let shift = (((a2 as i8 % 8) + 8) % 8) as u32; // smod 8
    (lhs.wrapping_shl(shift)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_shift_right(a1: u8, a2: u8) -> u8 {
    let lhs = a1 as i8;
    let shift = (((a2 as i8 % 8) + 8) % 8) as u32; // smod 8
    (lhs.wrapping_shr(shift)) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_neg(a: u8) -> u8 {
    let arg = a as i8;
    (arg.wrapping_neg()) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_abs(a: u8) -> u8 {
    let arg = a as i8;
    // With -fwrapv, INT8_MIN maps to INT8_MIN
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u8
}

#[inline(always)]
pub unsafe fn lean_int8_dec_eq(a1: u8, a2: u8) -> bool {
    (a1 as i8) == (a2 as i8)
}

#[inline(always)]
pub unsafe fn lean_int8_dec_lt(a1: u8, a2: u8) -> bool {
    (a1 as i8) < (a2 as i8)
}

#[inline(always)]
pub unsafe fn lean_int8_dec_le(a1: u8, a2: u8) -> bool {
    (a1 as i8) <= (a2 as i8)
}

// --- Int16 Operations ---

#[inline(always)]
pub unsafe fn lean_int16_add(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_add(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_sub(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_sub(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_mul(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (lhs.wrapping_mul(rhs)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_div(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_mod(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let rhs = a2 as i16;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_land(a1: u16, a2: u16) -> u16 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int16_lor(a1: u16, a2: u16) -> u16 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int16_xor(a1: u16, a2: u16) -> u16 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int16_complement(a: u16) -> u16 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int16_shift_left(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let shift = (((a2 as i16 % 16) + 16) % 16) as u32; // smod 16
    (lhs.wrapping_shl(shift)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_shift_right(a1: u16, a2: u16) -> u16 {
    let lhs = a1 as i16;
    let shift = (((a2 as i16 % 16) + 16) % 16) as u32; // smod 16
    (lhs.wrapping_shr(shift)) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_neg(a: u16) -> u16 {
    let arg = a as i16;
    (arg.wrapping_neg()) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_abs(a: u16) -> u16 {
    let arg = a as i16;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u16
}

#[inline(always)]
pub unsafe fn lean_int16_dec_eq(a1: u16, a2: u16) -> bool {
    (a1 as i16) == (a2 as i16)
}

#[inline(always)]
pub unsafe fn lean_int16_dec_lt(a1: u16, a2: u16) -> bool {
    (a1 as i16) < (a2 as i16)
}

#[inline(always)]
pub unsafe fn lean_int16_dec_le(a1: u16, a2: u16) -> bool {
    (a1 as i16) <= (a2 as i16)
}

// --- Int32 Operations ---

#[inline(always)]
pub unsafe fn lean_int32_add(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_add(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_sub(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_sub(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_mul(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (lhs.wrapping_mul(rhs)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_div(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_mod(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let rhs = a2 as i32;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_land(a1: u32, a2: u32) -> u32 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int32_lor(a1: u32, a2: u32) -> u32 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int32_xor(a1: u32, a2: u32) -> u32 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int32_complement(a: u32) -> u32 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int32_shift_left(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32; // smod 32
    (lhs.wrapping_shl(shift)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_shift_right(a1: u32, a2: u32) -> u32 {
    let lhs = a1 as i32;
    let shift = (((a2 as i32 % 32) + 32) % 32) as u32; // smod 32
    (lhs.wrapping_shr(shift)) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_neg(a: u32) -> u32 {
    let arg = a as i32;
    (arg.wrapping_neg()) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_abs(a: u32) -> u32 {
    let arg = a as i32;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u32
}

#[inline(always)]
pub unsafe fn lean_int32_dec_eq(a1: u32, a2: u32) -> bool {
    (a1 as i32) == (a2 as i32)
}

#[inline(always)]
pub unsafe fn lean_int32_dec_lt(a1: u32, a2: u32) -> bool {
    (a1 as i32) < (a2 as i32)
}

#[inline(always)]
pub unsafe fn lean_int32_dec_le(a1: u32, a2: u32) -> bool {
    (a1 as i32) <= (a2 as i32)
}

// --- Int64 Operations ---

#[inline(always)]
pub unsafe fn lean_int64_add(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_add(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_sub(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_sub(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_mul(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (lhs.wrapping_mul(rhs)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_div(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (if rhs == 0 { 0 } else { lhs / rhs }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_mod(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let rhs = a2 as i64;
    (if rhs == 0 { lhs } else { lhs % rhs }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_land(a1: u64, a2: u64) -> u64 {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_int64_lor(a1: u64, a2: u64) -> u64 {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_int64_xor(a1: u64, a2: u64) -> u64 {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_int64_complement(a: u64) -> u64 {
    !a
}

#[inline(always)]
pub unsafe fn lean_int64_shift_left(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32; // smod 64
    (lhs.wrapping_shl(shift)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_shift_right(a1: u64, a2: u64) -> u64 {
    let lhs = a1 as i64;
    let shift = (((a2 as i64 % 64) + 64) % 64) as u32; // smod 64
    (lhs.wrapping_shr(shift)) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_neg(a: u64) -> u64 {
    let arg = a as i64;
    (arg.wrapping_neg()) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_abs(a: u64) -> u64 {
    let arg = a as i64;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as u64
}

#[inline(always)]
pub unsafe fn lean_int64_dec_eq(a1: u64, a2: u64) -> bool {
    (a1 as i64) == (a2 as i64)
}

#[inline(always)]
pub unsafe fn lean_int64_dec_lt(a1: u64, a2: u64) -> bool {
    (a1 as i64) < (a2 as i64)
}

#[inline(always)]
pub unsafe fn lean_int64_dec_le(a1: u64, a2: u64) -> bool {
    (a1 as i64) <= (a2 as i64)
}

// --- ISize Operations ---

#[inline(always)]
pub unsafe fn lean_isize_add(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_add(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_sub(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_sub(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_mul(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (lhs.wrapping_mul(rhs)) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_div(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (if rhs == 0 { 0 } else { lhs / rhs }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_mod(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    let rhs = a2 as isize;
    (if rhs == 0 { lhs } else { lhs % rhs }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_land(a1: size_t, a2: size_t) -> size_t {
    a1 & a2
}

#[inline(always)]
pub unsafe fn lean_isize_lor(a1: size_t, a2: size_t) -> size_t {
    a1 | a2
}

#[inline(always)]
pub unsafe fn lean_isize_xor(a1: size_t, a2: size_t) -> size_t {
    a1 ^ a2
}

#[inline(always)]
pub unsafe fn lean_isize_complement(a: size_t) -> size_t {
    !a
}

#[inline(always)]
pub unsafe fn lean_isize_shift_left(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    lhs.wrapping_shl(a2 as u32) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_shift_right(a1: size_t, a2: size_t) -> size_t {
    let lhs = a1 as isize;
    lhs.wrapping_shr(a2 as u32) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_neg(a: size_t) -> size_t {
    let arg = a as isize;
    (arg.wrapping_neg()) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_abs(a: size_t) -> size_t {
    let arg = a as isize;
    (if arg < 0 { arg.wrapping_neg() } else { arg }) as size_t
}

#[inline(always)]
pub unsafe fn lean_isize_dec_eq(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) == (a2 as isize)
}

#[inline(always)]
pub unsafe fn lean_isize_dec_lt(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) < (a2 as isize)
}

#[inline(always)]
pub unsafe fn lean_isize_dec_le(a1: size_t, a2: size_t) -> bool {
    (a1 as isize) <= (a2 as isize)
}

// ============================================================================
