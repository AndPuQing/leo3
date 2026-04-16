use leo3::prelude::*;

#[leanmodule(name = "FixtureModule")]
#[allow(unused_imports)]
mod fixture_module {
    use leo3::prelude::*;

    #[leanfn(name = "fixture_add")]
    pub fn add(a: u64, b: u64) -> u64 {
        a + b
    }

    #[leanfn(name = "fixture_banner")]
    pub fn banner(name: String, count: i32) -> String {
        format!("{name} has {count} ticks")
    }
}
