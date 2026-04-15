use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
struct BadGenericImpl;

#[leanclass]
impl<T> BadGenericImpl {
    fn bad(&self, value: T) {
        let _ = value;
    }
}

fn main() {}
