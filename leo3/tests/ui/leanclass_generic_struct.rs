#[leo3_macros::leanclass]
struct BadGeneric<T> {
    value: T,
}

fn main() {}
