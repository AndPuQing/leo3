use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
struct BadTuple;

#[leanclass]
impl BadTuple {
    fn bad(&self, value: (u64, bool, String)) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
