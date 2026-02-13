//! Core implementation for leo3-build-config.
//!
//! This module is usable from both `lib.rs` (`mod impl_;`) and
//! `build.rs` (`#[path = "src/impl_.rs"] mod impl_;`) — the PyO3 pattern.
//! It accesses the errors module via `super::errors`.

// Some items are only used from build.rs or lib.rs, not both.
#![allow(dead_code)]

use super::errors::{self, bail, ensure, Context};
use std::cmp::Ordering;
use std::env;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;

/// Maximum minor version for `cargo:rustc-check-cfg` generation.
pub const CFG_MAX_MINOR: u32 = 40;

// ---------------------------------------------------------------------------
// LeanVersion
// ---------------------------------------------------------------------------

/// Parsed Lean version (e.g. 4.25.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl fmt::Display for LeanVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl FromStr for LeanVersion {
    type Err = errors::Error;

    fn from_str(s: &str) -> errors::Result<Self> {
        let parts: Vec<&str> = s.split('.').collect();
        ensure!(
            parts.len() >= 3,
            "invalid version '{}': expected major.minor.patch",
            s
        );
        let major = parts[0]
            .parse::<u32>()
            .map_err(|_| errors::Error::new(format!("invalid major version '{}'", parts[0])))?;
        let minor = parts[1]
            .parse::<u32>()
            .map_err(|_| errors::Error::new(format!("invalid minor version '{}'", parts[1])))?;
        // Patch may have a pre-release suffix (e.g. "0-nightly-2026-02-13-rev2")
        let patch_str = parts[2].split('-').next().unwrap_or(parts[2]);
        let patch = patch_str
            .parse::<u32>()
            .map_err(|_| errors::Error::new(format!("invalid patch version '{}'", parts[2])))?;
        Ok(LeanVersion {
            major,
            minor,
            patch,
        })
    }
}

impl Ord for LeanVersion {
    fn cmp(&self, other: &Self) -> Ordering {
        self.major
            .cmp(&other.major)
            .then(self.minor.cmp(&other.minor))
            .then(self.patch.cmp(&other.patch))
    }
}

impl PartialOrd for LeanVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// ---------------------------------------------------------------------------
// LeanConfig
// ---------------------------------------------------------------------------

/// Configuration for a detected Lean4 installation.
#[derive(Debug, Clone)]
pub struct LeanConfig {
    pub lean_home: PathBuf,
    pub lean_lib_dir: PathBuf,
    pub lean_include_dir: PathBuf,
    pub version: LeanVersion,
    pub shared: bool,
    pub pointer_width: Option<u32>,
}

// ---------------------------------------------------------------------------
// CrossCompileConfig
// ---------------------------------------------------------------------------

/// Cross-compilation configuration read from environment variables.
pub struct CrossCompileConfig {
    pub lib_dir: PathBuf,
    pub version: LeanVersion,
}

impl CrossCompileConfig {
    /// Read cross-compile config from `LEO3_CROSS_LIB_DIR` and `LEO3_CROSS_LEAN_VERSION`.
    pub fn from_env() -> errors::Result<Self> {
        let lib_dir = env::var("LEO3_CROSS_LIB_DIR")
            .map_err(|_| errors::Error::new("LEO3_CROSS_LIB_DIR not set"))?;
        let version_str = env::var("LEO3_CROSS_LEAN_VERSION")
            .map_err(|_| errors::Error::new("LEO3_CROSS_LEAN_VERSION not set"))?;
        let version = version_str
            .parse::<LeanVersion>()
            .context("parsing LEO3_CROSS_LEAN_VERSION")?;
        Ok(CrossCompileConfig {
            lib_dir: PathBuf::from(lib_dir),
            version,
        })
    }

    /// Convert into a full `LeanConfig`.
    pub fn into_lean_config(self) -> errors::Result<LeanConfig> {
        let lib_dir = &self.lib_dir;
        ensure!(
            lib_dir.exists(),
            "LEO3_CROSS_LIB_DIR does not exist: {}",
            lib_dir.display()
        );
        // For cross-compile, lean_home and include_dir are best-effort
        let lean_home = lib_dir
            .parent()
            .and_then(|p| p.parent())
            .unwrap_or(lib_dir)
            .to_path_buf();
        let lean_include_dir = lean_home.join("include");
        let shared = has_shared_libs(lib_dir);
        Ok(LeanConfig {
            lean_home,
            lean_lib_dir: self.lib_dir,
            lean_include_dir,
            version: self.version,
            shared,
            pointer_width: None,
        })
    }
}

// ---------------------------------------------------------------------------
// Detection functions
// ---------------------------------------------------------------------------

/// Main entry point: detect Lean4 configuration.
///
/// Tries cross-compile config first, then env vars, lake, elan, PATH.
pub fn detect_lean_config() -> errors::Result<LeanConfig> {
    if let Ok(cross) = CrossCompileConfig::from_env() {
        return cross.into_lean_config();
    }
    detect_from_env()
        .or_else(|_| detect_from_lake())
        .or_else(|_| detect_from_elan())
        .or_else(|_| detect_from_path())
}

/// Try to detect Lean from the `LEAN_HOME` environment variable.
fn detect_from_env() -> errors::Result<LeanConfig> {
    let lean_home = env::var("LEAN_HOME").map_err(|_| errors::Error::new("LEAN_HOME not set"))?;
    validate_lean_installation(&PathBuf::from(lean_home))
}

/// Try to detect Lean from the `lake` command.
fn detect_from_lake() -> errors::Result<LeanConfig> {
    let output = Command::new("lake")
        .arg("--version")
        .output()
        .context("failed to run lake")?;
    if !output.status.success() {
        bail!("lake command failed");
    }
    let output = Command::new("lake")
        .arg("env")
        .arg("printenv")
        .arg("LEAN_HOME")
        .output()
        .context("failed to get LEAN_HOME from lake")?;
    let lean_home = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if lean_home.is_empty() {
        bail!("lake did not provide LEAN_HOME");
    }
    validate_lean_installation(&PathBuf::from(lean_home))
}

/// Try to detect Lean from the `elan` toolchain manager.
fn detect_from_elan() -> errors::Result<LeanConfig> {
    let output = Command::new("elan")
        .arg("which")
        .arg("lean")
        .output()
        .context("failed to run elan")?;
    if !output.status.success() {
        bail!("elan command failed");
    }
    let lean_path = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let lean_home = resolve_lean_home(Path::new(&lean_path))?;
    validate_lean_installation(&lean_home)
}

/// Try to detect Lean from PATH.
///
/// Uses `where.exe` on Windows, `which` on Unix.
fn detect_from_path() -> errors::Result<LeanConfig> {
    let (cmd, arg) = if cfg!(target_os = "windows") {
        ("where.exe", "lean")
    } else {
        ("which", "lean")
    };
    let output = Command::new(cmd)
        .arg(arg)
        .output()
        .context("failed to find lean in PATH")?;
    if !output.status.success() {
        bail!("lean not found in PATH");
    }
    // `where.exe` may return multiple lines; take the first.
    let lean_path = String::from_utf8_lossy(&output.stdout)
        .lines()
        .next()
        .unwrap_or("")
        .trim()
        .to_string();
    let lean_home = resolve_lean_home(Path::new(&lean_path))?;
    validate_lean_installation(&lean_home)
}

/// Resolve the real Lean home directory from a lean binary path.
///
/// Uses `lean --print-prefix` which works correctly even when the binary
/// is an elan proxy (e.g. `~/.elan/bin/lean`). Falls back to the
/// parent-of-parent heuristic if `--print-prefix` fails.
fn resolve_lean_home(lean_bin: &Path) -> errors::Result<PathBuf> {
    if let Ok(output) = Command::new(lean_bin).arg("--print-prefix").output() {
        if output.status.success() {
            let prefix = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !prefix.is_empty() {
                return Ok(PathBuf::from(prefix));
            }
        }
    }
    // Fallback: assume <lean_home>/bin/lean layout
    lean_bin
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .context("could not determine LEAN_HOME from binary path")
}
/// Validate a Lean installation directory and build a `LeanConfig`.
///
/// Respects `LEAN_LIB_DIR` and `LEAN_INCLUDE_DIR` env var overrides.
fn validate_lean_installation(lean_home: &Path) -> errors::Result<LeanConfig> {
    ensure!(
        lean_home.exists(),
        "Lean home does not exist: {}",
        lean_home.display()
    );

    let lean_include_dir = match env::var("LEAN_INCLUDE_DIR") {
        Ok(dir) => PathBuf::from(dir),
        Err(_) => lean_home.join("include"),
    };
    let lean_lib_dir = match env::var("LEAN_LIB_DIR") {
        Ok(dir) => PathBuf::from(dir),
        Err(_) => lean_home.join("lib").join("lean"),
    };

    ensure!(
        lean_include_dir.exists(),
        "include directory not found: {}",
        lean_include_dir.display()
    );

    let lean_bin = lean_home.join("bin").join("lean");
    let version = get_lean_version(&lean_bin)?;
    let shared = has_shared_libs(&lean_lib_dir);

    Ok(LeanConfig {
        lean_home: lean_home.to_path_buf(),
        lean_lib_dir,
        lean_include_dir,
        version,
        shared,
        pointer_width: None,
    })
}

/// Run `lean --version` and parse the output into a `LeanVersion`.
fn get_lean_version(lean_bin: &Path) -> errors::Result<LeanVersion> {
    let output = Command::new(lean_bin)
        .arg("--version")
        .output()
        .context("failed to run lean --version")?;
    if !output.status.success() {
        bail!("lean --version failed");
    }
    let version_output = String::from_utf8_lossy(&output.stdout);
    // Output looks like "Lean (version 4.25.2, ...)"
    let version_str = version_output
        .split_whitespace()
        .find_map(|word| {
            let trimmed = word.trim_end_matches(',');
            if trimmed.starts_with('4') && trimmed.contains('.') {
                Some(trimmed.to_string())
            } else {
                None
            }
        })
        .context("could not parse Lean version from output")?;
    version_str.parse::<LeanVersion>()
}

/// Check whether the lib directory contains shared libraries.
fn has_shared_libs(lib_dir: &Path) -> bool {
    lib_dir.join("libleanshared.so").exists()
        || lib_dir.join("libleanshared.dylib").exists()
        || lib_dir.join("libleanshared.dll.a").exists()
        || lib_dir.join("leanshared.dll").exists()
}

// ---------------------------------------------------------------------------
// Serialization — key=value text format
// ---------------------------------------------------------------------------

impl LeanConfig {
    /// Serialize to a key=value text format.
    pub fn to_writer(&self, writer: &mut impl std::io::Write) -> std::io::Result<()> {
        writeln!(writer, "lean_home={}", self.lean_home.display())?;
        writeln!(writer, "lean_lib_dir={}", self.lean_lib_dir.display())?;
        writeln!(
            writer,
            "lean_include_dir={}",
            self.lean_include_dir.display()
        )?;
        writeln!(writer, "version={}", self.version)?;
        writeln!(writer, "shared={}", self.shared)?;
        match self.pointer_width {
            Some(w) => writeln!(writer, "pointer_width={}", w)?,
            None => writeln!(writer, "pointer_width=")?,
        }
        Ok(())
    }

    /// Deserialize from a key=value text format.
    pub fn from_reader(reader: impl std::io::BufRead) -> errors::Result<Self> {
        let mut lean_home = None;
        let mut lean_lib_dir = None;
        let mut lean_include_dir = None;
        let mut version = None;
        let mut shared = None;
        let mut pointer_width: Option<Option<u32>> = None;

        for line in reader.lines() {
            let line = line.map_err(|e| errors::Error::with_source("reading config", e))?;
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let (key, value) = line
                .split_once('=')
                .context(format!("invalid config line: {}", line))?;
            match key {
                "lean_home" => lean_home = Some(PathBuf::from(value)),
                "lean_lib_dir" => lean_lib_dir = Some(PathBuf::from(value)),
                "lean_include_dir" => lean_include_dir = Some(PathBuf::from(value)),
                "version" => version = Some(value.parse::<LeanVersion>()?),
                "shared" => shared = Some(value == "true"),
                "pointer_width" => {
                    pointer_width = Some(if value.is_empty() {
                        None
                    } else {
                        Some(value.parse::<u32>().map_err(|_| {
                            errors::Error::new(format!("invalid pointer_width '{}'", value))
                        })?)
                    });
                }
                _ => {} // ignore unknown keys for forward compat
            }
        }

        Ok(LeanConfig {
            lean_home: lean_home.context("missing lean_home")?,
            lean_lib_dir: lean_lib_dir.context("missing lean_lib_dir")?,
            lean_include_dir: lean_include_dir.context("missing lean_include_dir")?,
            version: version.context("missing version")?,
            shared: shared.context("missing shared")?,
            pointer_width: pointer_width.context("missing pointer_width")?,
        })
    }
}

// ---------------------------------------------------------------------------
// Hex serialization for Cargo DEP_* transport
// ---------------------------------------------------------------------------

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0xf) as usize] as char);
    }
    out
}

fn hex_decode(hex: &str) -> errors::Result<Vec<u8>> {
    ensure!(hex.len().is_multiple_of(2), "hex string has odd length");
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    for i in (0..bytes.len()).step_by(2) {
        let hi = hex_nibble(bytes[i])?;
        let lo = hex_nibble(bytes[i + 1])?;
        out.push((hi << 4) | lo);
    }
    Ok(out)
}

fn hex_nibble(b: u8) -> errors::Result<u8> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(b - b'a' + 10),
        b'A'..=b'F' => Ok(b - b'A' + 10),
        _ => Err(errors::Error::new(format!(
            "invalid hex char '{}'",
            b as char
        ))),
    }
}

impl LeanConfig {
    /// Hex-encode the key=value representation for Cargo `DEP_*` env transport.
    pub fn to_cargo_dep_env(&self) -> String {
        let mut buf = Vec::new();
        // to_writer only fails on I/O; Vec<u8> never fails.
        self.to_writer(&mut buf).expect("write to Vec failed");
        hex_encode(&buf)
    }

    /// Decode a hex-encoded config previously produced by `to_cargo_dep_env`.
    pub fn from_cargo_dep_env(hex: &str) -> errors::Result<Self> {
        let bytes = hex_decode(hex)?;
        let cursor = std::io::Cursor::new(bytes);
        Self::from_reader(std::io::BufReader::new(cursor))
    }
}

// ---------------------------------------------------------------------------
// Build script helpers
// ---------------------------------------------------------------------------

/// Print `cargo:rustc-check-cfg` for all supported `lean_4_N` flags.
pub fn print_expected_cfgs() {
    for minor in 0..=CFG_MAX_MINOR {
        println!("cargo:rustc-check-cfg=cfg(lean_4_{})", minor);
    }
}

/// Print `cargo:rerun-if-env-changed` for every env var we inspect.
pub fn print_rerun_if_env_changed() {
    for var in &[
        "LEO3_NO_LEAN",
        "LEAN_HOME",
        "ELAN_HOME",
        "LEAN_LIB_DIR",
        "LEAN_INCLUDE_DIR",
        "LEO3_CONFIG_FILE",
        "LEO3_CROSS_LIB_DIR",
        "LEO3_CROSS_LEAN_VERSION",
        "PATH",
    ] {
        println!("cargo:rerun-if-env-changed={}", var);
    }
}

/// Emit `cargo:rustc-link-*` directives for linking against Lean.
pub fn emit_link_config(config: &LeanConfig) {
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();

    println!(
        "cargo:rustc-link-search=native={}",
        config.lean_lib_dir.display()
    );

    if target_os == "windows" {
        let bin_dir = config.lean_home.join("bin");
        println!("cargo:rustc-link-search=native={}", bin_dir.display());
    }

    let has_init_shared = if target_os == "windows" {
        config.lean_lib_dir.join("libInit_shared.dll.a").exists()
    } else {
        config.lean_lib_dir.join("libInit_shared.so").exists()
            || config.lean_lib_dir.join("libInit_shared.dylib").exists()
    };

    let has_leanshared_2 = if target_os == "windows" {
        config.lean_lib_dir.join("libleanshared_2.dll.a").exists()
    } else {
        config.lean_lib_dir.join("libleanshared_2.so").exists()
            || config.lean_lib_dir.join("libleanshared_2.dylib").exists()
    };

    let has_leanshared_1 = if target_os == "windows" {
        config.lean_lib_dir.join("libleanshared_1.dll.a").exists()
    } else {
        config.lean_lib_dir.join("libleanshared_1.so").exists()
            || config.lean_lib_dir.join("libleanshared_1.dylib").exists()
    };

    if target_os == "windows" {
        if has_init_shared {
            println!("cargo:rustc-link-lib=dylib:+verbatim=libInit_shared.dll.a");
        }
        if has_leanshared_2 {
            println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared_2.dll.a");
        }
        if has_leanshared_1 {
            println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared_1.dll.a");
        }
        println!("cargo:rustc-link-lib=dylib:+verbatim=libleanshared.dll.a");
    } else {
        if has_init_shared {
            println!("cargo:rustc-link-lib=dylib=Init_shared");
        }
        if has_leanshared_2 {
            println!("cargo:rustc-link-lib=dylib=leanshared_2");
        }
        if has_leanshared_1 {
            println!("cargo:rustc-link-lib=dylib=leanshared_1");
        }
        println!("cargo:rustc-link-lib=dylib=leanshared");
    }

    if target_os == "windows" {
        println!("cargo:rustc-link-lib=dylib=Ws2_32");
        println!("cargo:rustc-link-lib=dylib=Bcrypt");
        println!("cargo:rustc-link-lib=dylib=Userenv");
    }

    if target_os != "windows" {
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            config.lean_lib_dir.display()
        );
    }

    println!("cargo:include={}", config.lean_include_dir.display());
}

/// Emit `cargo:rustc-cfg=lean_4_N` for the detected version and all earlier minors.
pub fn emit_version_cfgs(config: &LeanConfig) {
    if config.version.major != 4 {
        return;
    }
    for v in 0..=config.version.minor {
        println!("cargo:rustc-cfg=lean_4_{}", v);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_version_parse() {
        let v: LeanVersion = "4.25.2".parse().unwrap();
        assert_eq!(v.major, 4);
        assert_eq!(v.minor, 25);
        assert_eq!(v.patch, 2);
        assert_eq!(v.to_string(), "4.25.2");

        // Pre-release suffix (nightly builds)
        let v: LeanVersion = "4.29.0-nightly-2026-02-13-rev2".parse().unwrap();
        assert_eq!(v.major, 4);
        assert_eq!(v.minor, 29);
        assert_eq!(v.patch, 0);

        assert!("abc".parse::<LeanVersion>().is_err());
        assert!("4".parse::<LeanVersion>().is_err());
        assert!("4.25".parse::<LeanVersion>().is_err());
    }

    #[test]
    fn test_lean_version_ord() {
        let v1: LeanVersion = "4.20.0".parse().unwrap();
        let v2: LeanVersion = "4.25.2".parse().unwrap();
        let v3: LeanVersion = "4.25.3".parse().unwrap();
        assert!(v1 < v2);
        assert!(v2 < v3);
        assert_eq!(v2, "4.25.2".parse().unwrap());
    }

    #[test]
    fn test_lean_config_serialization_roundtrip() {
        let config = LeanConfig {
            lean_home: PathBuf::from("/opt/lean"),
            lean_lib_dir: PathBuf::from("/opt/lean/lib/lean"),
            lean_include_dir: PathBuf::from("/opt/lean/include"),
            version: "4.25.2".parse().unwrap(),
            shared: true,
            pointer_width: Some(64),
        };
        let mut buf = Vec::new();
        config.to_writer(&mut buf).unwrap();
        let restored =
            LeanConfig::from_reader(std::io::BufReader::new(std::io::Cursor::new(buf))).unwrap();
        assert_eq!(restored.lean_home, config.lean_home);
        assert_eq!(restored.lean_lib_dir, config.lean_lib_dir);
        assert_eq!(restored.lean_include_dir, config.lean_include_dir);
        assert_eq!(restored.version, config.version);
        assert_eq!(restored.shared, config.shared);
        assert_eq!(restored.pointer_width, config.pointer_width);
    }

    #[test]
    fn test_cargo_dep_env_roundtrip() {
        let config = LeanConfig {
            lean_home: PathBuf::from("/home/user/.elan/toolchains/leanprover-lean4-v4.25.2"),
            lean_lib_dir: PathBuf::from(
                "/home/user/.elan/toolchains/leanprover-lean4-v4.25.2/lib/lean",
            ),
            lean_include_dir: PathBuf::from(
                "/home/user/.elan/toolchains/leanprover-lean4-v4.25.2/include",
            ),
            version: "4.25.2".parse().unwrap(),
            shared: false,
            pointer_width: None,
        };
        let hex = config.to_cargo_dep_env();
        let restored = LeanConfig::from_cargo_dep_env(&hex).unwrap();
        assert_eq!(restored.lean_home, config.lean_home);
        assert_eq!(restored.version, config.version);
        assert_eq!(restored.shared, config.shared);
        assert_eq!(restored.pointer_width, config.pointer_width);
    }

    #[test]
    fn test_print_expected_cfgs_count() {
        // Verify the loop would generate CFG_MAX_MINOR + 1 lines (0..=40 = 41).
        let count = (0..=CFG_MAX_MINOR).count();
        assert_eq!(count, 41);
    }

    #[test]
    fn test_hex_roundtrip() {
        let data = b"hello world\nversion=4.25.2\n";
        let encoded = hex_encode(data);
        let decoded = hex_decode(&encoded).unwrap();
        assert_eq!(decoded, data);
    }

    #[test]
    fn test_hex_decode_invalid() {
        assert!(hex_decode("0").is_err()); // odd length
        assert!(hex_decode("zz").is_err()); // invalid chars
    }
}
