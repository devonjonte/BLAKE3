//! The build checks the proof of the code it links.
//!
//! 1. `proof/push_arm_meets.ndjson.gz` is Lean's export of the theorem `push_arm_meets` with everything it
//!    depends on. nanoda, an independent checker of Lean proofs written in Rust, checks every declaration
//!    in it, permitting Lean's three axioms and no other. If one does not check, the build fails.
//! 2. The checker prints the theorem's statement back from what it checked. It must be, to the letter,
//!    `proof/push_arm_meets.statement.txt`: the text a reader read.
//! 3. The instruction words are taken from the checked definition `push_arm_code` that the statement
//!    names, and those words are what is assembled and linked. No other source of the code exists here.

use nanoda_lib::util::Config;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

const THEOREM: &str = "push_arm_meets";
const CODE: &str = "push_arm_code";
const SYMBOL: &str = "b3l_push";

fn main() {
    println!("cargo:rerun-if-changed=proof");
    println!("cargo:rerun-if-changed=build.rs");
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let t0 = Instant::now();

    // The export, unpacked.
    let export = out.join("export.ndjson");
    {
        let packed = std::fs::File::open("proof/push_arm_meets.ndjson.gz").expect("the proof is in the crate");
        let mut reader = flate2::read::GzDecoder::new(std::io::BufReader::new(packed));
        let mut file = std::io::BufWriter::new(std::fs::File::create(&export).unwrap());
        std::io::copy(&mut reader, &mut file).expect("the proof unpacks");
        file.flush().unwrap();
    }
    let unpacked = t0.elapsed();

    // 1. Every declaration checks; only Lean's three axioms are allowed.
    let printed = out.join("checked.txt");
    std::fs::File::create(&printed).unwrap();
    let config = out.join("checker.json");
    std::fs::write(
        &config,
        format!(
            r#"{{"export_file_path": {export:?}, "use_stdin": false, "num_threads": 4,
                "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
                "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
                "pp_declars": [{THEOREM:?}, {CODE:?}], "pp_to_stdout": false, "pp_output_path": {printed:?},
                "pp_options": {{"proofs": false, "width": 110}}, "print_success_message": false}}"#
        ),
    )
    .unwrap();
    let t1 = Instant::now();
    let cfg = Config::try_from(Path::new(&config)).expect("the checker's configuration");
    let mut destination = cfg.get_pp_destination().expect("a place for the statement");
    let (file, skipped) = cfg.to_export_file().expect("the export parses, and names no axiom but Lean's three");
    assert!(skipped.is_empty(), "the export names axioms that are not permitted: {skipped:?}");
    let declarations = file.declars.len();
    file.check_all_declars(); // panics, and so fails the build, if a declaration does not check
    let errors = file.pp_selected_declars(destination.as_mut());
    drop(destination);
    let checked = t1.elapsed();

    // 2. The statement that was checked is the statement that was read.
    let text = std::fs::read_to_string(&printed).unwrap();
    let paragraph = |start: &str| -> String {
        let at = text.find(start).unwrap_or_else(|| panic!("the checker printed no `{start}` ({errors:?})"));
        text[at..].split("\n\n").next().unwrap().trim_end().to_string()
    };
    let statement = paragraph(&format!("theorem {THEOREM} "));
    let read = std::fs::read_to_string("proof/push_arm_meets.statement.txt").expect("the statement to read");
    assert!(
        statement == read.trim_end(),
        "the theorem that checks is not the statement in proof/push_arm_meets.statement.txt:\n{statement}"
    );
    assert!(statement.contains(&format!("Arm64.FnCode.holds {CODE} prog")), "the statement names the code");

    // 3. The words of the checked definition are the code.
    let code = paragraph(&format!("def {CODE} "));
    let marker = "BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat ";
    let words: Vec<u32> = code
        .match_indices(marker)
        .map(|(at, _)| {
            let digits: String = code[at + marker.len()..].chars().take_while(|c| c.is_ascii_digit()).collect();
            digits.parse::<u32>().expect("an instruction word is 32 bits")
        })
        .collect();
    assert!(!words.is_empty() && code.matches("List.cons").count() == words.len(), "every word of the code is read");
    assert!(code.contains(&format!("Arm64.FnCode.ofFn {SYMBOL:?}")), "the code is the function's");

    if std::env::var("CARGO_CFG_TARGET_ARCH").unwrap() == "aarch64" {
        let symbol = if std::env::var("CARGO_CFG_TARGET_VENDOR").unwrap() == "apple" { format!("_{SYMBOL}") } else { SYMBOL.to_string() };
        let mut source = format!("\t.text\n\t.globl {symbol}\n\t.p2align 2\n{symbol}:\n");
        for word in &words {
            source += &format!("\t.long 0x{word:08x}\n");
        }
        let path = out.join("push.S");
        std::fs::write(&path, source).unwrap();
        cc::Build::new().file(&path).compile("checked_push");
    }
    println!(
        "cargo:warning=proof checked: {declarations} declarations in {:.1} s (unpacked in {:.1} s); {} instruction words linked from the theorem",
        checked.as_secs_f64(),
        unpacked.as_secs_f64(),
        words.len()
    );
}
