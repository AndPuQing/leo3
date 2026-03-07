//! Minimal test for #[leanclass] macro expansion

#![cfg(feature = "macros")]

use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
#[allow(dead_code)]
struct Simple {
    value: i32,
}

#[leanclass]
impl Simple {
    fn new(val: i32) -> Self {
        Simple { value: val }
    }
}
