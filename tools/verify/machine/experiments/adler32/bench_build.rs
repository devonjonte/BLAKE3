use std::{env, fs, path::PathBuf, process::Command};

fn main() {
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let padding: usize = env::var("ODE_PADDING").unwrap_or_else(|_| "0".into()).parse().unwrap();
    assert!(padding <= 4096 && padding % 16 == 0);
    let asm = format!(".text\n.balign 64\n.space {padding}, 0x90\n{}", fs::read_to_string("function.S").unwrap());
    fs::write(out.join("padded.S"), asm).unwrap();
    let cc = env::var("CC").unwrap_or_else(|_| "cc".into());
    assert!(Command::new(cc).args(["-c"]).arg(out.join("padded.S")).arg("-o").arg(out.join("function.o")).status().unwrap().success());
    assert!(Command::new("ar").arg("crs").arg(out.join("libode.a")).arg(out.join("function.o")).status().unwrap().success());
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=ode");
    println!("cargo:rerun-if-changed=function.S");
    println!("cargo:rerun-if-changed=text.bin");
    println!("cargo:rerun-if-env-changed=ODE_PADDING");
    println!("cargo:rustc-env=ODE_PADDING={padding}");
    println!(
        "cargo:rustc-env=ODE_RUSTC={}",
        String::from_utf8(Command::new(env::var("RUSTC").unwrap()).arg("--version").output().unwrap().stdout).unwrap().trim()
    );
}
