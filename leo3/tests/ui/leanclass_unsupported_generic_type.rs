#[derive(Clone)]
#[leo3_macros::leanclass]
struct BadGeneric;

#[leo3_macros::leanclass]
impl BadGeneric {
    fn bad(&self, value: std::collections::HashMap<String, u64>) -> i32 {
        let _ = value;
        0
    }
}

fn main() {}
