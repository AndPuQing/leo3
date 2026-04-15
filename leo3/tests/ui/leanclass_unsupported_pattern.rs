use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
struct BadPattern;

#[leanclass]
impl BadPattern {
    fn bad(&self, (left, right): (u64, bool)) -> i32 {
        let _ = (left, right);
        0
    }
}

fn main() {}
