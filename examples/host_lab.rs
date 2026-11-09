//! Clock studies on the Mac. Run from a fresh result directory, with one
//! argument: `clocks`, `kpc`, `events`, or nothing for all three.
//!
//! - `clocks`: zooko/measure-clocks3 at a pinned commit, run as written;
//!   then a control that brackets a known amount of work the way
//!   bench-hashes' samplers do (a counts read, a wall read, the work, a
//!   wall read, a counts read), so the reads' own share of the counted
//!   interval is known.
//! - `kpc`: tools/studies/kpc_probe.c, what root buys a read: direct
//!   counter reads, the cost of each read interface, the configurable
//!   events around known work.
//! - `events`: old against new, the chosen events around the final
//!   hashes (tools/studies/events_sampler.rs, judged by
//!   tools/studies/events_judge.rs).
//!
//! Root comes through `sudo -n` at one fixed path the Mac's sudoers names
//! (tools/runner/README.md, "Root for a probe"); a refusal is recorded as
//! a result.
use std::path::{Path, PathBuf};
use std::process::Command;

const CLOCKS_TOOL: &str = "https://github.com/zooko/measure-clocks3";
const CLOCKS_TOOL_COMMIT: &str = "5005425b906de1a7a70421681407f1a91b79632b";
const BENCH: &str = "https://github.com/servil-software-factory/bench-hashes";
const BENCH_COMMIT: &str = "9994de190259648ede82f7c5e4dbac4f1534a41d";
const LIBRARY: &str = "https://github.com/servil-software-factory/BLAKE3";
const OLD: &str = "0b5bf7b71cb5f850067fa4182d9a3c724d7e5710";
const NEW: &str = "f13933376c8b8236adaeffe6aa9d25ad25f2af24";
const PAIRS: usize = 4;
const FIXED: &str = "/Users/Shared/bench-runner/root-probes/kpc-probe";

fn main() {
    let root = std::env::current_dir().expect("the study has a result directory");
    let what = std::env::args().nth(1).unwrap_or_else(|| "all".to_owned());
    assert!(matches!(what.as_str(), "all" | "clocks" | "kpc" | "events"), "choose clocks, kpc, events, or nothing for all");
    if matches!(what.as_str(), "all" | "clocks") {
        clocks_study(&root);
    }
    if matches!(what.as_str(), "all" | "kpc") {
        kpc_probe(&root);
    }
    if matches!(what.as_str(), "all" | "events") {
        events_study(&root);
    }
}

fn run(args: &[&str], cwd: &Path) {
    let status = Command::new(args[0]).args(&args[1..]).current_dir(cwd).status().expect("the command starts");
    assert!(status.success(), "{args:?} failed in {}", cwd.display());
}

fn stdout(args: &[&str], cwd: &Path) -> String {
    let output = Command::new(args[0]).args(&args[1..]).current_dir(cwd).output().expect("the command starts");
    assert!(output.status.success(), "{args:?} failed in {}", cwd.display());
    String::from_utf8(output.stdout).unwrap()
}

fn fetch(url: &str, commit: &str, into: &Path) {
    run(&["git", "clone", "--no-checkout", url, into.to_str().unwrap()], into.parent().unwrap());
    run(&["git", "fetch", url, commit], into);
    run(&["git", "checkout", "--quiet", commit], into);
    assert_eq!(stdout(&["git", "rev-parse", "HEAD"], into).trim(), commit, "the checkout is the pinned commit");
}

fn bench_checkout(root: &Path) -> PathBuf {
    let bench = root.join("bench");
    if !bench.exists() {
        fetch(BENCH, BENCH_COMMIT, &bench);
    }
    bench
}

fn write_project(dir: &Path, name: &str, deps: &str, main_rs: &str) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("Cargo.toml"), format!("[package]\nname=\"{name}\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\n{deps}[profile.release]\nlto=\"fat\"\n[workspace]\n")).unwrap();
    std::fs::write(dir.join("src/main.rs"), main_rs).unwrap();
}

/// Run `binary` as root at the one path the sudoers names. Its stdout
/// becomes `label` in `root`, written by this unprivileged process, its
/// exit and stderr `label.err`; a refusal is a recorded result.
fn as_root(root: &Path, binary: &Path, label: &str) -> bool {
    let fixed = Path::new(FIXED);
    let placed = std::fs::create_dir_all(fixed.parent().unwrap()).and_then(|()| std::fs::copy(binary, fixed));
    let mut text = match &placed {
        Err(e) => format!("could not place the probe at {}: {e}\n", fixed.display()).into_bytes(),
        Ok(_) => Vec::new(),
    };
    let output = Command::new("sudo").arg("-n").arg(FIXED).current_dir(root).output().unwrap();
    text.extend_from_slice(&output.stdout);
    std::fs::write(root.join(label), &text).unwrap();
    std::fs::write(root.join(format!("{label}.err")), format!("exit: {:?}\n{}", output.status.code(), String::from_utf8_lossy(&output.stderr))).unwrap();
    placed.is_ok() && output.status.success()
}

fn clocks_study(root: &Path) {
    let tool = root.join("measure-clocks3");
    fetch(CLOCKS_TOOL, CLOCKS_TOOL_COMMIT, &tool);
    run(&["cargo", "build", "--release"], &tool);
    run(&["sh", "run-measurement.sh"], &tool);
    run(&["sh", "run-measurement.sh", "--overthread"], &tool);
    let results: Vec<String> = std::fs::read_dir(tool.join("results")).unwrap().map(|e| e.unwrap().path().to_str().unwrap().to_owned()).collect();
    let summary = Command::new("python3").arg("parse-results.py").args(&results).current_dir(&tool).output().unwrap();
    assert!(summary.status.success(), "parse-results.py");
    std::fs::write(root.join("measure-clocks3-summary.txt"), summary.stdout).unwrap();

    let bench = bench_checkout(root);
    let control = root.join("bracket-control");
    write_project(&control, "bracket-control", &format!("clocks={{path=\"{}\"}}\n", bench.join("clocks").display()), include_str!("../tools/studies/bracket_control.rs"));
    run(&["cargo", "build", "--release"], &control);
    let text = stdout(&[control.join("target/release/bracket-control").to_str().unwrap()], root);
    std::fs::write(root.join("bracket-control.txt"), &text).unwrap();
    print!("{text}");
}

fn kpc_probe(root: &Path) {
    let probe = root.join("kpc-probe");
    run(&["cc", "-O2", "-o", probe.to_str().unwrap(), concat!(env!("CARGO_MANIFEST_DIR"), "/tools/studies/kpc_probe.c")], root);
    let output = Command::new(&probe).current_dir(root).output().unwrap();
    std::fs::write(root.join("kpc-probe-user.txt"), &output.stdout).unwrap();
    println!("== kpc-probe-user.txt\n{}", String::from_utf8_lossy(&output.stdout));
    as_root(root, &probe, "kpc-probe-root.txt");
    println!("== kpc-probe-root.txt\n{}", std::fs::read_to_string(root.join("kpc-probe-root.txt")).unwrap());
}

/// Old against new: PAIRS pairs of runs in alternating order, each pair
/// with a fresh link layout (a distinct crate metadata hash), both
/// samplers built from exact checkouts; the judge takes the files in
/// pair order.
fn events_study(root: &Path) {
    let library = Path::new(env!("CARGO_MANIFEST_DIR"));
    let bench = bench_checkout(root);
    let mut identity = format!("old {OLD}\nnew {NEW}\nbench {BENCH_COMMIT}\nrustc {}", stdout(&["rustc", "--version"], root));
    for (side, commit) in [("old", OLD), ("new", NEW)] {
        let lib = root.join(format!("lib-{side}"));
        run(&["git", "fetch", LIBRARY, commit], library);
        run(&["git", "worktree", "add", "--detach", lib.to_str().unwrap(), commit], library);
        assert_eq!(stdout(&["git", "rev-parse", "HEAD"], &lib).trim(), commit);
        identity.push_str(&format!("{side} tree clean: {}\n", stdout(&["git", "status", "--porcelain"], &lib).is_empty()));
        write_project(
            &root.join(format!("sampler-{side}")),
            "events-sampler",
            &format!("blake3-servil={{path=\"{}\"}}\nclocks={{path=\"{}\"}}\n", lib.display(), bench.join("clocks").display()),
            include_str!("../tools/studies/events_sampler.rs"),
        );
    }
    std::fs::write(root.join("events-identity.txt"), identity).unwrap();
    let judge = root.join("judge");
    write_project(&judge, "events-judge", &format!("clocks={{path=\"{}\"}}\n", bench.join("clocks").display()), include_str!("../tools/studies/events_judge.rs"));
    run(&["cargo", "build", "--release"], &judge);
    let mut files = Vec::new();
    for pair in 0..PAIRS {
        let order = if pair % 2 == 0 { ["old", "new"] } else { ["new", "old"] };
        let mut pair_files = [String::new(), String::new()];
        for side in order {
            let target = root.join(format!("target-{side}-{pair}"));
            let status = Command::new("cargo")
                .args(["build", "--release"])
                .env("CARGO_TARGET_DIR", &target)
                .env("RUSTFLAGS", format!("-C metadata=events_pair_{pair}"))
                .current_dir(root.join(format!("sampler-{side}")))
                .status()
                .unwrap();
            assert!(status.success(), "building the {side} sampler, pair {pair}");
            let label = format!("events-{side}-{pair}.tsv");
            assert!(as_root(root, &target.join("release/events-sampler"), &label), "{label}: see its .err");
            pair_files[usize::from(side == "new")] = root.join(&label).to_str().unwrap().to_owned();
        }
        files.extend(pair_files);
    }
    let output = Command::new(judge.join("target/release/events-judge")).args(&files).output().unwrap();
    assert!(output.status.success(), "judge: {}", String::from_utf8_lossy(&output.stderr));
    std::fs::write(root.join("events-judgment.txt"), &output.stdout).unwrap();
    print!("{}", String::from_utf8_lossy(&output.stdout));
}
