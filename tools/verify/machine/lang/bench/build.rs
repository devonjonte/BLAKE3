// The two printings of the Lean functions, as assembly: `way_a.s` is what rustc made of the printed
// Rust (made before this build, by run.sh), `way_b.S` is what Lean printed itself.
fn main() {
    let dir = std::env::var("LAB_ASM").expect("LAB_ASM: where way_a.s and way_b.S are");
    cc::Build::new().file(format!("{dir}/way_a.s")).file(format!("{dir}/way_b.S")).compile("lab_ways");
    println!("cargo::rerun-if-changed={dir}/way_a.s");
    println!("cargo::rerun-if-changed={dir}/way_b.S");
}
