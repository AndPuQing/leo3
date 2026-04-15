use leo3::prelude::*;
#[derive(Clone)]
#[leanclass]
struct BadGeneric;

#[leanclass]
impl BadGeneric {
    fn bad(&self, value: std::collections::HashMap<String, u64>) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
