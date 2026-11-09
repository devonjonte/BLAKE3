//! The build version: the crate's version with what names this build's code
//! (Zooko, November 9, 2026: as much as fits in the version). The source
//! version, in Cargo.toml, is a release's `X.Y.Z+<its code commit>` on the
//! release commit alone, and `X.Y.Z+dev` on the commits after it
//! (tools/gen-ver.py). A build of the release commit is named by that
//! version alone. Any other build appends its commit, and a dirty tree the
//! Git tree id of its working tree, every file Git does not ignore as it
//! is now:
//!
//!     0.8.0+b3c5efc7…              the release commit, clean
//!     0.8.0+dev.<commit>           a later commit, clean
//!     0.8.0+dev.<commit>.dirty.<tree id>
//!
//! (semver build metadata: dot-separated ASCII letters, digits and hyphens.)
//! The commit and tree come from the checkout's Git where the crate's
//! parent directory, the library's, is the top of a work tree (a clone, a
//! worktree, Cargo's checkout of a git dependency), else from the crate's
//! `.cargo_vcs_info.json` (a package: its commit, and `.dirty` without a
//! tree where it was packaged dirty), else nothing is appended. Shared by
//! version/build.rs and its test (tests/build_version.rs).

use std::path::{Path, PathBuf};
use std::process::Command;

/// Cargo's marker in its checkout of a git dependency: no change of ours.
const CARGO_MARKER: &str = ".cargo-ok";

fn git(dir: &Path, args: &[&str], index: Option<&Path>) -> Option<String> {
    let mut command = Command::new("git");
    command.arg("-C").arg(dir).args(args);
    if let Some(index) = index {
        command.env("GIT_INDEX_FILE", index);
    }
    let out = command.output().ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

/// The build version of the version crate at `krate`, whose source version
/// is `version`, and the paths whose change changes it (for
/// rerun-if-changed).
pub fn build_version(krate: &Path, version: &str, scratch: &Path) -> (String, Vec<PathBuf>) {
    let package = || (from_package_info(krate, version), vec![krate.join(".cargo_vcs_info.json")]);
    let Some(dir) = krate.parent() else {
        return package();
    };
    // Everything Git is asked once, in one process: each costs a few ms,
    // paid on every edit.
    let Some(answers) = git(dir, &["rev-parse", "--show-toplevel", "--git-dir", "--git-common-dir", "--git-path", "index", "HEAD", "HEAD^{tree}"], None) else {
        return package();
    };
    let absolute = |p: &str| if Path::new(p).is_absolute() { PathBuf::from(p) } else { dir.join(p) };
    let [top, git_dir, common, real_index, commit, head_tree] = answers.lines().collect::<Vec<_>>()[..] else {
        return package();
    };
    if Path::new(top).canonicalize().ok() != dir.canonicalize().ok() {
        return package();
    }
    // The working tree as Git would commit it, through an index of our own.
    // A copy of the checkout's index keeps Git's record of unchanged files,
    // so only changed ones are read.
    let index = scratch.join("build-version-index");
    let _ = std::fs::remove_file(&index);
    let prepared = match absolute(real_index) {
        real if real.exists() => std::fs::copy(real, &index).ok().map(|_| String::new()),
        _ => git(dir, &["read-tree", "HEAD"], Some(&index)),
    };
    let exclude = format!(":(exclude){CARGO_MARKER}");
    let tree = prepared.and_then(|_| git(dir, &["add", "-A", "--", ".", &exclude], Some(&index))).and_then(|_| git(dir, &["write-tree"], Some(&index)));
    let _ = std::fs::remove_file(&index);
    let clean = tree.as_deref() == Some(head_tree);
    let release = version.split_once('+').is_some_and(|(_, named)| named.len() == 40 && git(dir, &["rev-parse", "HEAD^"], None).as_deref() == Some(named));
    let name = match (clean, release) {
        (true, true) => version.to_owned(),
        (true, false) => format!("{version}.{commit}"),
        (false, _) => format!("{version}.{commit}.dirty{}", tree.map_or(String::new(), |t| format!(".{t}"))),
    };
    (name, watched(dir, &absolute(git_dir), &absolute(common)))
}

/// A package's build: its commit and dirty flag as `cargo package` wrote them.
fn from_package_info(dir: &Path, version: &str) -> String {
    let Ok(info) = std::fs::read_to_string(dir.join(".cargo_vcs_info.json")) else {
        return version.to_owned();
    };
    let field = |name: &str| info.split(&format!("\"{name}\"")).nth(1).map(|rest| rest.trim_start_matches([' ', ':', '"']).to_owned());
    let Some(commit) = field("sha1").map(|s| s.chars().take_while(char::is_ascii_hexdigit).collect::<String>()) else {
        return version.to_owned();
    };
    let dirty = field("dirty").is_some_and(|s| s.starts_with("true"));
    if version.ends_with("+dev") || dirty { format!("{version}.{commit}{}", if dirty { ".dirty" } else { "" }) } else { version.to_owned() }
}

/// What a commit, a checkout or an edit changes: HEAD, the index, the
/// reflog, the refs, and every file Git tracks (a new untracked file is
/// seen at the next of these).
fn watched(dir: &Path, git_dir: &Path, common: &Path) -> Vec<PathBuf> {
    let mut paths = vec![git_dir.join("HEAD"), git_dir.join("index"), git_dir.join("logs/HEAD"), common.join("refs"), common.join("packed-refs")];
    if let Some(files) = git(dir, &["ls-files"], None) {
        paths.extend(files.lines().map(|f| dir.join(f)));
    }
    paths.retain(|p| p.exists());
    paths
}
