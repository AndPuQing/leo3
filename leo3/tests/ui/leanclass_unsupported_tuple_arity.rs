#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadTuple;

#[leo3_macros::leanclass]
impl BadTuple {
    fn bad(&self, value: (u64, bool, String)) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
