#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadGenericMethod;

#[leo3_macros::leanclass]
impl BadGenericMethod {
    fn bad<T>(&self, value: T) {
        let _ = value;
    }
}

fn main() {}
