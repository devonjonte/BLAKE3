//! blake3-servil's build version, as `blake3_servil::BUILD_VERSION`.
#![no_std]

/// This build's version: the crate's version, and for any build but a
/// release's own commit, the commit built and, from a dirty tree, the Git
/// tree id of its working tree, e.g. `0.8.0+dev.<commit>.dirty.<tree>`
/// (`version/build_version.rs`). `b3sum --version` and the C library's
/// `b3_version()` print it.
pub const BUILD_VERSION: &str = env!("BLAKE3_SERVIL_BUILD_VERSION");
