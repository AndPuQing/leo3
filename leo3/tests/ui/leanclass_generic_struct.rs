use leo3::prelude::*;

#[leanclass]
struct BadGeneric<T> {
    value: T,
}

fn main() {}
