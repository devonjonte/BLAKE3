//! probe/shared-after-gap driver: bench-hashes probe/shared-after-gap
//! (abea417) on this fork, the shared copies concurrent (as the benchmark
//! runs them) and one after the other (HB_DUO_SERIAL), two runs each,
//! alternating, traced. Question: is a shared copy after a gap faster than
//! solo because the two copies of the same code warm each other?
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn checked(command: &mut Command) {
    eprintln!("driver: {command:?}");
    assert!(command.status().expect("run a diagnostic command").success(), "diagnostic command succeeds");
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out = std::env::current_dir().expect("the runner's output directory");
    let bench = root.join("bench-hashes");
    checked(Command::new("git").arg("-C").arg(&bench).args(["fetch", "--quiet", "origin"]));
    checked(Command::new("git").arg("-C").arg(&bench).args(["checkout", "--quiet", "--detach", "89f9588"]));
    let built = Command::new("/opt/homebrew/bin/pypy3").arg(root.join("tools/perf_regress.py")).arg("--root").arg(root)
        .args(["build", "--side", "bench", "--commit", "b06c074"]).stderr(Stdio::inherit()).output().expect("build");
    assert!(built.status.success(), "the benchmark builds");
    let exe = PathBuf::from(String::from_utf8(built.stdout).unwrap().trim());
    // Round two (job 809): the shared sample before the solo one (HB_SHARED_FIRST), against the usual order.
    for (name, serial) in [("solo-first-1", false), ("shared-first-1", true), ("shared-first-2", true), ("solo-first-2", false)] {
        let folder = out.join(name);
        std::fs::create_dir(&folder).unwrap();
        let mut command = Command::new(&exe);
        command.current_dir(&folder).args(["--contenders", "blake3-servil-st,sha256-ring,sha1dc", "--points",
            "64 B,1 KiB,4 KiB,16 KiB,64 KiB,idle 64 B,idle 4 KiB,idle 16 KiB,lent 4 KiB,lent 16 KiB", "--rounds", "48", "--trace-clocks"])
            .arg(folder.join("trace.csv"));
        if serial { command.env("HB_SHARED_FIRST", "1"); }
        checked(&mut command);
    }
}
