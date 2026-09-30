//! Native validation driver for benchmark/API alignment. The Mac runner's
//! example handler runs this GitHub-sourced diagnostic while its installed
//! benchmark builder awaits the speeds.py installation fix. Hashing source
//! remains at 9cea065 (identical to 5cfa2b4); only this example is replaced.
//! Each build uses an explicit fork and benchmark commit. Every timed loop
//! and count read belongs to the benchmark's clocks crate.
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn checked(command: &mut Command) {
    eprintln!("driver: {command:?}");
    assert!(command.status().expect("run diagnostic command").success(), "diagnostic command succeeds");
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out = std::env::current_dir().expect("runner output directory");
    let bench = root.join("bench-hashes");
    assert!(bench.join(".git").exists(), "runner keeps a benchmark checkout");
    checked(Command::new("git").arg("-C").arg(&bench).args(["fetch", "--quiet", "origin"]));
    let jobs = [
        ("old-1", "f3515ab", "1820efb", false),
        ("new-1", "9cf2787", "1820efb", false),
        ("new-2", "9cf2787", "1820efb", false),
        ("old-2", "f3515ab", "1820efb", false),
    ];
    let python = "/opt/homebrew/bin/pypy3";
    assert!(Path::new(python).exists(), "Mac runner's PyPy is installed");
    for (label, bench_commit, fork_commit, all) in jobs {
        checked(Command::new("git").arg("-C").arg(&bench).args(["checkout", "--quiet", "--detach", bench_commit]));
        let built = Command::new(python).arg(root.join("tools/perf_regress.py"))
            .arg("--root").arg(root).args(["build", "--side", "bench", "--commit", fork_commit])
            .stderr(Stdio::inherit()).output().expect("build exact benchmark pair");
        assert!(built.status.success(), "build {label} succeeds");
        let exe = PathBuf::from(String::from_utf8(built.stdout).expect("executable path UTF-8").trim());
        assert!(exe.is_file(), "builder prints an executable path");
        let folder = out.join(label);
        std::fs::create_dir(&folder).expect("fresh run directory");
        let mut command = Command::new(exe);
        command.current_dir(&folder).arg("--trace-clocks").arg(folder.join("trace.csv"));
        if all { command.arg("--all"); }
        checked(&mut command);
    }
}
