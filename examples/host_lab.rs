//! Clock study on the Mac: zooko/measure-clocks3 at a pinned commit, run as
//! written, then a control that brackets a known amount of work the way
//! bench-hashes' samplers do (a counts read, a wall read, the work, a wall
//! read, a counts read), so the reads' own share of the counted interval
//! is known. Then tools/studies/kpc_probe.c: what root buys a read (direct
//! counter reads, the cost of each read interface, the configurable
//! events around known work). Run from a fresh result directory.
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

    // What root buys: kpc_probe runs as the runner's user, then as root
    // through `sudo -n` at one fixed path, the one the Mac's sudoers may
    // name (tools/runner/README.md, "Root for a probe"); a refusal is
    // recorded as a result.
    let probe = root.join("kpc-probe");
    run(&["cc", "-O2", "-o", probe.to_str().unwrap(), concat!(env!("CARGO_MANIFEST_DIR"), "/tools/studies/kpc_probe.c")], &root);
    let fixed = Path::new("/Users/Shared/bench-runner/root-probes/kpc-probe");
    let placed = std::fs::create_dir_all(fixed.parent().unwrap()).and_then(|()| std::fs::copy(&probe, fixed));
    let mut as_root = Command::new("sudo");
    as_root.args(["-n", fixed.to_str().unwrap()]);
    for (label, mut command) in [("kpc-probe-user.txt", Command::new(&probe)), ("kpc-probe-root.txt", as_root)] {
        let mut text = match &placed {
            Err(e) if label.contains("root") => format!("could not place the probe at {}: {e}\n", fixed.display()).into_bytes(),
            _ => Vec::new(),
        };
        let output = command.current_dir(&root).output().unwrap();
        text.extend_from_slice(&output.stdout);
        text.extend_from_slice(format!("\nexit: {:?}\nstderr:\n", output.status.code()).as_bytes());
        text.extend_from_slice(&output.stderr);
        std::fs::write(root.join(label), &text).unwrap();
        println!("== {label}\n{}", String::from_utf8_lossy(&text));
    }
}
