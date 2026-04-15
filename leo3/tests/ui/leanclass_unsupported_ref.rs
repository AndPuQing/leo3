use leo3::prelude::*;

#[derive(Clone)]
#[leanclass]
struct BadRef;

#[leanclass]
impl BadRef {
    fn bad(&self, value: &str) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
