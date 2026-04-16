#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadPattern;

#[leo3_macros::leanclass]
impl BadPattern {
    fn bad(&self, (left, right): (u64, bool)) -> i32 {
        let _ = (left, right);
        0
    }
}

fn main() {}
