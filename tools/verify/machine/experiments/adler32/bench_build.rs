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
    let probe = env::var_os("CARGO_FEATURE_PROBE").is_some();
    let deflate = if probe { "deflate-wide" } else { "deflate" };
    for (dir, lib) in [("zlib", "z"), ("zlib-ng", "z-ng"), ("libdeflate", deflate)] {
        let path = root.join("native").join(dir);
        assert!(path.join(format!("lib{lib}.a")).exists());
        println!("cargo:rustc-link-search=native={}", path.display());
        println!("cargo:rustc-link-lib=static={lib}");
    }
    if probe {
        // Experimental symbols bind to this executable's copied archive.
        println!("cargo:rustc-link-arg=-Wl,--exclude-libs,libdeflate-wide.a");
        let mut objects = Vec::new();
        for (width, prefix, reduce32, align, small, name) in [
            (64, 0, 0, 0, 0, "probe512"), (64, 1, 0, 0, 0, "probe512_one"),
            (32, 0, 0, 0, 0, "probe256"), (32, 1, 0, 0, 0, "probe256_one"),
            (64, 0, 1, 0, 0, "probe512_r32"), (64, 0, 1, 1, 0, "probe512_align"),
            (64, 0, 1, 1, 1, "probe512_small"),
        ] {
            let object = out.join(format!("{name}.o"));
            assert!(Command::new(&cc)
                .args(["-c", "-O3", "-DNDEBUG", "-fno-lto", "-mavx512bw", "-mavx512vl", "-mavx512vnni", "-mavx512dq"])
                .args([
                    format!("-DVL={width}"),
                    format!("-DONEPREFIX={prefix}"),
                    format!("-DREDUCE32={reduce32}"),
                    format!("-DALIGN_HEAD={align}"),
                    format!("-DSMALL_SEED={small}"),
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
        for (batch, split, name) in [(0, 0, "probe4096"), (1, 0, "probe4096_batch"), (0, 1, "probe4096_entry")] {
            let object = out.join(format!("{name}.c.o"));
            assert!(Command::new(&cc).args(["-c", "-O3", "-DNDEBUG", "-fno-lto"])
                .args([format!("-DBATCH4={batch}"), format!("-DENTRY_SPLIT={split}"), format!("-DPROBE_NAME={name}")])
                .arg("probe4096.c").arg("-o").arg(&object).status().unwrap().success());
            objects.push(object);
        }
        let object = out.join("raw4096.S.o");
        assert!(Command::new(&cc).args(["-c", "-O3", "-DNDEBUG", "-fno-lto"])
            .arg("raw4096.S").arg("-o").arg(&object).status().unwrap().success());
        objects.push(object);
        println!("cargo:rerun-if-changed=probe4096.c");
        println!("cargo:rerun-if-changed=raw4096.S");
        assert!(Command::new("ar").arg("crs").arg(out.join("libprobe.a")).args(objects).status().unwrap().success());
        println!("cargo:rustc-link-arg=-Wl,--exclude-libs,libprobe.a");
        println!("cargo:rustc-link-lib=static=probe");
        println!("cargo:rustc-link-search=native={}", root.join("native/isa-l").display());
        println!("cargo:rustc-link-lib=static=isal");
        println!("cargo:rerun-if-changed=probe.c");
        println!("cargo:rerun-if-changed=align.h");
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
