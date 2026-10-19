//! The shared library's soname (Linux) or install name (macOS) carries the
//! crate's major.minor, so a program built against one release cannot
//! load another's library and misread its `b3_hasher` layout unnoticed.
fn main() {
    let version = std::env::var("CARGO_PKG_VERSION").unwrap();
    let mut parts = version.split('.');
    let (major, minor) = (parts.next().unwrap(), parts.next().unwrap());
    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    if os == "linux" {
        println!("cargo::rustc-cdylib-link-arg=-Wl,-soname,libb3_servil.so.{major}.{minor}");
    } else if os == "macos" {
        println!("cargo::rustc-cdylib-link-arg=-Wl,-install_name,@rpath/libb3_servil.{major}.{minor}.dylib");
        println!("cargo::rustc-cdylib-link-arg=-Wl,-compatibility_version,{major}.{minor}");
        println!("cargo::rustc-cdylib-link-arg=-Wl,-current_version,{version}");
    }
}
