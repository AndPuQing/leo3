use leo3::types::LeanHashMap;

fn main() {
    let _ = std::any::type_name::<LeanHashMap<'static, (), ()>>();
}
