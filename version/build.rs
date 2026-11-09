//! The build version (build_version.rs) of the repository this crate sits
//! in, or of its package. A crate of its own so that its build script,
//! which reruns on every edit to the repository's files, is the only one
//! that does: the library's assembles the kernels, and reruns when they
//! change alone.

mod build_version;

use std::env;
use std::path::PathBuf;

fn main() {
    let dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let scratch = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let (name, watched) = build_version::build_version(&dir, &env::var("CARGO_PKG_VERSION").unwrap(), &scratch);
    println!("cargo::rustc-env=BLAKE3_SERVIL_BUILD_VERSION={name}");
    println!("cargo::rerun-if-changed=build_version.rs");
    for path in watched {
        println!("cargo::rerun-if-changed={}", path.display());
    }
}
