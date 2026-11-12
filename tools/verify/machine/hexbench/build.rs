// The kernel for this architecture: the file the compiler printed (hex_x86.S is a copy of what
// lang/prove.sh prints as hex.S; ../arm/hex_neon.S is what arm/prove_arm.sh checks).
fn main() {
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let file = if arch == "aarch64" { "../arm/hex_neon.S" } else { "hex_x86.S" };
    cc::Build::new().file(file).compile("hexkernel");
    println!("cargo:rerun-if-changed={file}");
}
