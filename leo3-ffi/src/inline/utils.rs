//! Small helpers shared by inline FFI submodules.

// ========================================================================
// Branch Prediction Hints (corresponding to Lean's LEAN_LIKELY)
// ========================================================================

/// Hint to compiler that condition is likely to be true
#[inline(always)]
#[allow(dead_code)]
pub(crate) const fn likely(b: bool) -> bool {
    // In stable Rust, we can't use intrinsics, so this is a no-op
    // The compiler's own branch prediction is usually good enough
    // If you're on nightly, you could use: core::intrinsics::likely(b)
    b
}

/// Hint to compiler that condition is unlikely to be true
#[inline(always)]
#[allow(dead_code)]
pub(crate) const fn unlikely(b: bool) -> bool {
    // In stable Rust, we can't use intrinsics, so this is a no-op
    // If you're on nightly, you could use: core::intrinsics::unlikely(b)
    b
}
