//! Lean Range type wrapper.
//!
//! The `Range` type represents a series of consecutive natural numbers with a start, stop, and step.

use crate::err::LeanResult;
use crate::ffi;
use crate::instance::LeanBound;
use crate::types::LeanNat;

/// A Lean Range object.
///
/// Range in Lean4 is defined as a structure:
/// ```lean
/// structure Std.Range where
///   start : Nat := 0
///   stop  : Nat
///   step  : Nat := 1
///   step_pos : 0 < step
/// ```
///
/// `Range` represents a series of consecutive natural numbers from `start` to `stop-1`,
/// incrementing by `step`. It's primarily used for iteration in `for` loops.
///
/// # Runtime Representation
///
/// At runtime, only the three natural number fields are stored - the proof that `step > 0`
/// is erased. The constructor has tag 0 with 3 object fields (start, stop, step).
///
/// # Syntax
///
/// In Lean4, Range has special syntax:
/// - `[:n]` - range from 0 to n-1 with step 1
/// - `[m:n]` - range from m to n-1 with step 1
/// - `[m:n:s]` - range from m to n-1 with step s
///
/// # Examples
///
/// Common uses:
/// - `[:10]` - numbers 0 through 9
/// - `[5:10]` - numbers 5 through 9
/// - `[0:10:2]` - even numbers 0, 2, 4, 6, 8
pub struct LeanRange {
    _private: (),
}

impl LeanRange {
    /// Create a Range with start, stop, and step.
    ///
    /// # Lean4 Reference
    /// Corresponds to the `Range` constructor or `[start:stop:step]` syntax.
    ///
    /// # Parameters
    ///
    /// - `start`: First value in the range (inclusive)
    /// - `stop`: Upper bound of the range (exclusive)
    /// - `step`: Increment between values
    ///
    /// # Safety
    ///
    /// This assumes `step > 0`. In Lean4, this is enforced by a proof `step_pos : 0 < step`,
    /// but at runtime the proof is erased and not verified.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use leo3::prelude::*;
    ///
    /// leo3::with_lean(|lean| {
    ///     let start = LeanNat::from_usize(lean, 0)?;
    ///     let stop = LeanNat::from_usize(lean, 10)?;
    ///     let step = LeanNat::from_usize(lean, 2)?;
    ///     let range = LeanRange::new(start, stop, step)?;
    ///     // Represents [0:10:2] = 0, 2, 4, 6, 8
    ///     Ok(())
    /// })
    /// ```
    pub fn new<'l>(
        start: LeanBound<'l, LeanNat>,
        stop: LeanBound<'l, LeanNat>,
        step: LeanBound<'l, LeanNat>,
    ) -> LeanResult<LeanBound<'l, Self>> {
        unsafe {
            let lean = start.lean_token();
            // Range is constructor 0 with 3 fields (start, stop, step; step_pos proof erased)
            let ptr = ffi::lean_alloc_ctor(0, 3, 0);
            ffi::lean_ctor_set(ptr, 0, start.into_ptr());
            ffi::lean_ctor_set(ptr, 1, stop.into_ptr());
            ffi::lean_ctor_set(ptr, 2, step.into_ptr());
            Ok(LeanBound::from_owned_ptr(lean, ptr))
        }
    }

    /// Create a Range from 0 to stop with step 1.
    ///
    /// # Lean4 Reference
    /// Corresponds to `[:stop]` syntax in Lean4.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let stop = LeanNat::from_usize(lean, 10)?;
    /// let range = LeanRange::mk(stop)?;
    /// // Represents [:10] = 0, 1, 2, ..., 9
    /// ```
    pub fn mk<'l>(stop: LeanBound<'l, LeanNat>) -> LeanResult<LeanBound<'l, Self>> {
        let lean = stop.lean_token();
        let start = LeanNat::from_usize(lean, 0)?;
        let step = LeanNat::from_usize(lean, 1)?;
        Self::new(start, stop, step)
    }

    /// Get the start value of the range.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Range.start` field access.
    pub fn start<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanNat> {
        unsafe {
            let lean = obj.lean_token();
            let start_ptr = ffi::lean_ctor_get(obj.as_ptr(), 0) as *mut ffi::lean_object;
            ffi::lean_inc(start_ptr);
            LeanBound::from_owned_ptr(lean, start_ptr)
        }
    }

    /// Get the stop value of the range.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Range.stop` field access.
    pub fn stop<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanNat> {
        unsafe {
            let lean = obj.lean_token();
            let stop_ptr = ffi::lean_ctor_get(obj.as_ptr(), 1) as *mut ffi::lean_object;
            ffi::lean_inc(stop_ptr);
            LeanBound::from_owned_ptr(lean, stop_ptr)
        }
    }

    /// Get the step value of the range.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Range.step` field access.
    pub fn step<'l>(obj: &LeanBound<'l, Self>) -> LeanBound<'l, LeanNat> {
        unsafe {
            let lean = obj.lean_token();
            let step_ptr = ffi::lean_ctor_get(obj.as_ptr(), 2) as *mut ffi::lean_object;
            ffi::lean_inc(step_ptr);
            LeanBound::from_owned_ptr(lean, step_ptr)
        }
    }

    /// Calculate the number of elements in the range.
    ///
    /// # Lean4 Reference
    /// Corresponds to `Range.size` in Lean4:
    /// ```lean
    /// def size (r : Range) : Nat := (r.stop - r.start + r.step - 1) / r.step
    /// ```
    ///
    /// # Formula
    ///
    /// The size is calculated as: `(stop - start + step - 1) / step`
    ///
    /// This formula correctly handles:
    /// - Empty ranges (when start >= stop): returns 0
    /// - Non-aligned ranges: rounds up to include the last step
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// // Range [0:10:3] has elements 0, 3, 6, 9 (size = 4)
    /// let range = LeanRange::new(zero, ten, three)?;
    /// let size = LeanRange::size(&range)?;
    /// ```
    pub fn size<'l>(obj: &LeanBound<'l, Self>) -> LeanResult<LeanBound<'l, LeanNat>> {
        let lean = obj.lean_token();
        let start = Self::start(obj);
        let stop = Self::stop(obj);
        let step = Self::step(obj);

        // Clone step for multiple uses
        let step_clone1 = unsafe {
            ffi::lean_inc(step.as_ptr());
            LeanBound::from_owned_ptr(lean, step.as_ptr())
        };
        let step_clone2 = unsafe {
            ffi::lean_inc(step.as_ptr());
            LeanBound::from_owned_ptr(lean, step.as_ptr())
        };

        // Calculate (stop - start + step - 1) / step
        let one = LeanNat::from_usize(lean, 1)?;

        // stop - start
        let diff = LeanNat::sub(stop, start)?;

        // diff + step
        let sum1 = LeanNat::add(diff, step_clone1)?;

        // sum1 - 1
        let sum2 = LeanNat::sub(sum1, one)?;

        // sum2 / step
        let size = LeanNat::div(sum2, step_clone2)?;

        Ok(size)
    }
}

// Implement Debug for convenient printing
impl<'l> std::fmt::Debug for LeanBound<'l, LeanRange> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanRange[...:...:...]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_size() {
        // Verify that LeanRange is zero-sized
        assert_eq!(std::mem::size_of::<LeanRange>(), 0);
    }
}
