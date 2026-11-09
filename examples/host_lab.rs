//! Clock study on the Mac: zooko/measure-clocks3 at a pinned commit, run as
//! written, then a control that brackets a known amount of work the way
//! bench-hashes' samplers do (a counts read, a wall read, the work, a wall
//! read, a counts read), so the reads' own share of the counted interval
//! is known. Run from a fresh result directory.
use std::path::Path;
use std::process::Command;

const CLOCKS_TOOL: &str = "https://github.com/zooko/measure-clocks3";
const CLOCKS_TOOL_COMMIT: &str = "5005425b906de1a7a70421681407f1a91b79632b";
const BENCH: &str = "https://github.com/servil-software-factory/bench-hashes";
const BENCH_COMMIT: &str = "9994de190259648ede82f7c5e4dbac4f1534a41d";

fn run(args: &[&str], cwd: &Path) {
    let status = Command::new(args[0]).args(&args[1..]).current_dir(cwd).status().expect("the command starts");
    assert!(status.success(), "{args:?} failed in {}", cwd.display());
}

fn fetch(url: &str, commit: &str, into: &Path) {
    run(&["git", "clone", "--no-checkout", url, into.to_str().unwrap()], into.parent().unwrap());
    run(&["git", "fetch", url, commit], into);
    run(&["git", "checkout", "--quiet", commit], into);
    let head = Command::new("git").args(["rev-parse", "HEAD"]).current_dir(into).output().unwrap();
    assert_eq!(String::from_utf8(head.stdout).unwrap().trim(), commit, "the checkout is the pinned commit");
}

fn main() {
    let root = std::env::current_dir().expect("the study has a result directory");
    let tool = root.join("measure-clocks3");
    fetch(CLOCKS_TOOL, CLOCKS_TOOL_COMMIT, &tool);
    run(&["cargo", "build", "--release"], &tool);
    run(&["sh", "run-measurement.sh"], &tool);
    run(&["sh", "run-measurement.sh", "--overthread"], &tool);
    let results: Vec<String> = std::fs::read_dir(tool.join("results")).unwrap().map(|e| e.unwrap().path().to_str().unwrap().to_owned()).collect();
    let summary = Command::new("python3").arg("parse-results.py").args(&results).current_dir(&tool).output().unwrap();
    assert!(summary.status.success(), "parse-results.py");
    std::fs::write(root.join("measure-clocks3-summary.txt"), summary.stdout).unwrap();

    let bench = root.join("bench");
    fetch(BENCH, BENCH_COMMIT, &bench);
    let control = root.join("bracket-control");
    std::fs::create_dir_all(control.join("src")).unwrap();
    std::fs::write(
        control.join("Cargo.toml"),
        format!("[package]\nname=\"bracket-control\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\nclocks={{path=\"{}\"}}\n[profile.release]\nlto=\"fat\"\n", bench.join("clocks").display()),
    )
    .unwrap();
    std::fs::write(control.join("src/main.rs"), include_str!("../tools/studies/bracket_control.rs")).unwrap();
    run(&["cargo", "build", "--release"], &control);
    let output = Command::new(control.join("target/release/bracket-control")).current_dir(&root).output().unwrap();
    assert!(output.status.success(), "bracket-control: {}", String::from_utf8_lossy(&output.stderr));
    std::fs::write(root.join("bracket-control.txt"), &output.stdout).unwrap();
    print!("{}", String::from_utf8_lossy(&output.stdout));
}
