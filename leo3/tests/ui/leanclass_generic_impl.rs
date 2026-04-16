#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadGenericImpl;

#[leo3_macros::leanclass]
impl<T> BadGenericImpl {
    fn bad(&self, value: T) {
        let _ = value;
    }
}

fn main() {}
