// The two designs as assembly, both printed by Lean from Ode sources: `stack.S` from ../lang/hasher.ode
// (push, merge, hash), `levels.S` from ../levels.ode (ladd, lroot, hash2). Made before this build by
// run_levels.sh.
fn main() {
    let dir = std::env::var("LAB_ASM").expect("LAB_ASM: where stack.S and levels.S are");
    cc::Build::new().file(format!("{dir}/stack.S")).file(format!("{dir}/levels.S")).compile("lab_levels");
    println!("cargo::rerun-if-changed={dir}/stack.S");
    println!("cargo::rerun-if-changed={dir}/levels.S");
}
