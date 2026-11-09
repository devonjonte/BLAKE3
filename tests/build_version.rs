//! The build version (version/build_version.rs), against a repository made
//! here: each expected name built from Git's own answers (the commit, the
//! tree that committing the dirty tree makes), never from the code under
//! test.

#[path = "../version/build_version.rs"]
mod build_version;

use std::path::Path;
use std::process::Command;

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["-c", "user.name=t", "-c", "user.email=t@t.invalid", "-c", "commit.gpgsign=false"])
        .args(args)
        .output()
        .unwrap();
    assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap().trim().to_owned()
}

struct Repo(std::path::PathBuf);

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn repo(name: &str) -> Repo {
    let dir = std::env::temp_dir().join(format!("blake3-servil-build-version-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    git(&dir, &["init", "-q"]);
    std::fs::write(dir.join("code.rs"), "one").unwrap();
    git(&dir, &["add", "code.rs"]);
    git(&dir, &["commit", "-q", "-m", "code"]);
    Repo(dir)
}

/// The name, its scratch index beside the repository (each test's own, as
/// build.rs's is its OUT_DIR).
fn name(dir: &Path, version: &str) -> String {
    let scratch = dir.with_extension("scratch");
    std::fs::create_dir_all(&scratch).unwrap();
    // The version crate's directory: inside the repository, `version/`
    // (ignored by its Git, as an empty directory is); for a package, the
    // package itself.
    let krate = if dir.join(".git").exists() { dir.join("version") } else { dir.to_owned() };
    std::fs::create_dir_all(&krate).unwrap();
    let name = build_version::build_version(&krate, version, &scratch).0;
    std::fs::remove_dir_all(&scratch).unwrap();
    name
}

#[test]
fn a_release_commit_is_named_by_its_version_alone() {
    let r = repo("release");
    let code = git(&r.0, &["rev-parse", "HEAD"]);
    std::fs::write(r.0.join("Cargo.toml"), "version").unwrap();
    git(&r.0, &["add", "Cargo.toml"]);
    git(&r.0, &["commit", "-q", "-m", "release"]);
    let version = format!("0.8.0+{code}");
    assert_eq!(name(&r.0, &version), version);
    // Its code commit carries the same version and is not the release.
    git(&r.0, &["checkout", "-q", "--detach", &code]);
    assert_eq!(name(&r.0, &version), format!("{version}.{code}"));
}

#[test]
fn a_later_commit_is_named_by_its_commit() {
    let r = repo("dev");
    let commit = git(&r.0, &["rev-parse", "HEAD"]);
    assert_eq!(name(&r.0, "0.8.0+dev"), format!("0.8.0+dev.{commit}"));
}

#[test]
fn a_dirty_tree_is_named_by_its_tree_id_and_cargos_marker_is_no_change() {
    let r = repo("dirty");
    let commit = git(&r.0, &["rev-parse", "HEAD"]);
    std::fs::write(r.0.join(".cargo-ok"), "{\"v\":1}").unwrap();
    assert_eq!(name(&r.0, "0.8.0+dev"), format!("0.8.0+dev.{commit}"), "Cargo's marker alone");
    std::fs::write(r.0.join("code.rs"), "two").unwrap();
    std::fs::write(r.0.join("new.rs"), "three").unwrap();
    let got = name(&r.0, "0.8.0+dev");
    // The tree that committing exactly this working tree makes.
    git(&r.0, &["add", "-A", "--", ".", ":(exclude).cargo-ok"]);
    git(&r.0, &["commit", "-q", "-m", "as it was"]);
    let tree = git(&r.0, &["rev-parse", "HEAD^{tree}"]);
    assert_eq!(got, format!("0.8.0+dev.{commit}.dirty.{tree}"));
    assert_ne!(tree, git(&r.0, &["rev-parse", "HEAD^^{tree}"]));
}

#[test]
fn a_package_is_named_from_its_vcs_info() {
    let dir = std::env::temp_dir().join(format!("blake3-servil-build-version-package-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let r = Repo(dir);
    let sha = "0123456789abcdef0123456789abcdef01234567";
    std::fs::write(r.0.join(".cargo_vcs_info.json"), format!("{{\n  \"git\": {{\n    \"sha1\": \"{sha}\",\n    \"dirty\": true\n  }}\n}}")).unwrap();
    assert_eq!(name(&r.0, "0.8.0+dev"), format!("0.8.0+dev.{sha}.dirty"));
    std::fs::write(r.0.join(".cargo_vcs_info.json"), format!("{{\"git\":{{\"sha1\":\"{sha}\"}}}}")).unwrap();
    assert_eq!(name(&r.0, "0.8.0+dev"), format!("0.8.0+dev.{sha}"));
    assert_eq!(name(&r.0, &format!("0.8.0+{sha}")), format!("0.8.0+{sha}"), "a clean release package");
}

#[test]
fn this_build_starts_with_the_crates_version() {
    assert!(blake3_servil::BUILD_VERSION.starts_with(env!("CARGO_PKG_VERSION")), "{}", blake3_servil::BUILD_VERSION);
}
