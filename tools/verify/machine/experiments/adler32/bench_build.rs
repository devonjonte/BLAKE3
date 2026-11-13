use std::{env, fs, path::PathBuf, process::Command};

fn main() {
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let padding: usize = env::var("ODE_PADDING").unwrap_or_else(|_| "0".into()).parse().unwrap();
    assert!(padding <= 4096 && padding % 16 == 0);
    let asm = format!(".text\n.balign 64\n.space {padding}, 0x90\n{}", fs::read_to_string("function.S").unwrap());
    fs::write(out.join("padded.S"), asm).unwrap();
    let cc = env::var("CC").unwrap_or_else(|_| "cc".into());
    assert!(Command::new(&cc).args(["-c"]).arg(out.join("padded.S")).arg("-o").arg(out.join("function.o")).status().unwrap().success());
    assert!(Command::new("ar").arg("crs").arg(out.join("libode.a")).arg(out.join("function.o")).status().unwrap().success());
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=ode");
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    for (dir, lib) in [("zlib", "z"), ("zlib-ng", "z-ng"), ("libdeflate", "deflate")] {
        let path = root.join("native").join(dir);
        assert!(path.join(format!("lib{lib}.a")).exists());
        println!("cargo:rustc-link-search=native={}", path.display());
        println!("cargo:rustc-link-lib=static={lib}");
    }
    if env::var_os("CARGO_FEATURE_PROBE").is_some() {
        let mut objects = Vec::new();
        for (width, prefix, name) in [(64, 0, "probe512"), (64, 1, "probe512_one"), (32, 0, "probe256"), (32, 1, "probe256_one")] {
            let object = out.join(format!("{name}.o"));
            assert!(Command::new(&cc)
                .args(["-c", "-O3", "-DNDEBUG", "-fno-lto", "-mavx512bw", "-mavx512vl", "-mavx512vnni", "-mavx512dq"])
                .args([
                    format!("-DVL={width}"),
                    format!("-DONEPREFIX={prefix}"),
                    format!("-DPROBE_NAME={name}"),
                    "-DCHUNK=16384".into(),
                    format!("-mprefer-vector-width={}", width * 8)
                ])
                .arg("probe.c")
                .arg("-o")
                .arg(&object)
                .status()
                .unwrap()
                .success());
            objects.push(object);
        }
        assert!(Command::new("ar").arg("crs").arg(out.join("libprobe.a")).args(objects).status().unwrap().success());
        println!("cargo:rustc-link-lib=static=probe");
        println!("cargo:rustc-link-search=native={}", root.join("native/isa-l").display());
        println!("cargo:rustc-link-lib=static=isal");
        println!("cargo:rerun-if-changed=probe.c");
    }
    println!("cargo:rerun-if-changed=function.S");
    println!("cargo:rerun-if-changed=text.bin");
    println!("cargo:rerun-if-env-changed=ODE_PADDING");
    println!("cargo:rustc-env=ODE_PADDING={padding}");
    println!(
        "cargo:rustc-env=ODE_RUSTC={}",
        String::from_utf8(Command::new(env::var("RUSTC").unwrap()).arg("--version").output().unwrap().stdout).unwrap().trim()
    );
}
