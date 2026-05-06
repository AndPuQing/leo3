//! Golden-path dynamic loading test for `#[leanmodule]`.

#![cfg(all(
    feature = "macros",
    feature = "module-loading",
    feature = "runtime-tests"
))]

use leo3::module::LeanModule;
use leo3::LeanError;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture_manifest() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("leanmodule_runtime_fixture")
        .join("Cargo.toml")
}

fn unique_target_dir() -> PathBuf {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_millis();
    std::env::temp_dir().join(format!(
        "leo3-leanmodule-fixture-{}-{}",
        std::process::id(),
        millis
    ))
}

fn dylib_name() -> &'static str {
    #[cfg(target_os = "linux")]
    {
        "libleanmodule_runtime_fixture.so"
    }
    #[cfg(target_os = "macos")]
    {
        "libleanmodule_runtime_fixture.dylib"
    }
    #[cfg(target_os = "windows")]
    {
        "leanmodule_runtime_fixture.dll"
    }
}

fn address_sanitizer_enabled() -> bool {
    std::env::var("RUSTFLAGS")
        .ok()
        .is_some_and(|flags| flags.contains("sanitizer=address"))
}

fn build_fixture() -> PathBuf {
    let target_dir = unique_target_dir();
    let status = Command::new("cargo")
        .arg("build")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(fixture_manifest())
        .env("CARGO_TARGET_DIR", &target_dir)
        .status()
        .expect("fixture cargo build should start");

    assert!(status.success(), "fixture cargo build failed: {status}");

    target_dir.join("debug").join(dylib_name())
}

#[test]
fn test_dynamic_module_fixture_builds() {
    if address_sanitizer_enabled() {
        return;
    }
    let dylib = build_fixture();
    assert!(
        dylib.is_file(),
        "expected built fixture at {}",
        dylib.display()
    );

    let _typecheck = |path: &Path, name: &str| LeanModule::load(path, name);
}

#[test]
fn test_dynamic_module_fixture_loads_and_calls_exports() {
    if address_sanitizer_enabled() {
        return;
    }
    let dylib = build_fixture();
    assert!(
        dylib.is_file(),
        "expected built fixture at {}",
        dylib.display()
    );

    let module = LeanModule::load(&dylib, "FixtureModule")
        .unwrap_or_else(|err| panic!("failed to load fixture {}: {err}", dylib.display()));

    assert_eq!(module.name(), "FixtureModule");

    leo3::with_lean(|lean| {
        let add = module
            .get_function("fixture_add", 2)
            .expect("fixture_add should be exported");
        let sum: u64 = add
            .call2(lean, 20_u64, 22_u64)
            .expect("fixture_add should execute successfully");
        assert_eq!(sum, 42);

        let banner = module
            .get_function("fixture_banner", 2)
            .expect("fixture_banner should be exported");
        let message: String = banner
            .call2(lean, String::from("orbiter"), 7_i32)
            .expect("fixture_banner should execute successfully");
        assert_eq!(message, "orbiter has 7 ticks");

        Ok::<_, LeanError>(())
    })
    .unwrap();
}
