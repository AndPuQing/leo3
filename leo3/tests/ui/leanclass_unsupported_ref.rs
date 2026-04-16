#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadRef;

#[leo3_macros::leanclass]
impl BadRef {
    fn bad(&self, value: &str) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
