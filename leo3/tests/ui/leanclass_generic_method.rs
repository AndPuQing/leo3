use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
struct BadGenericMethod;

#[leanclass]
impl BadGenericMethod {
    fn bad<T>(&self, value: T) {
        let _ = value;
    }
}

fn main() {}
