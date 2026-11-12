//! The build checks the proof of the code it links.
//!
//! 1. `proof/push_arm_meets.ndjson.gz` is Lean's export of the theorem `push_arm_meets` with everything it
//!    depends on. nanoda, an independent checker of Lean proofs written in Rust, checks every declaration
//!    in it, permitting Lean's three axioms and no other. If one does not check, the build fails.
//! 2. The checker prints back, from what it checked, the theorem's statement and **everything the statement
//!    rests on**: every constant its type names, and in turn every constant those rest on (a definition's
//!    type and body; an axiom's, a theorem's or an opaque constant's type; an inductive type whole). This
//!    build finds that set itself, from the export. The printed text must be, to the letter,
//!    `proof/push_arm_meets.checked.txt`, and begin with `proof/push_arm_meets.statement.txt`: the text a
//!    reader read. So an export that defines any word of the statement otherwise fails the build.
//! 3. The instruction words are taken from the checked definition `push_arm_code` that the statement
//!    names, and those words are what is assembled and linked. No other source of the code exists here.

use nanoda_lib::util::Config;
use serde_json::Value;
use std::collections::{HashMap, HashSet};
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

const THEOREM: &str = "push_arm_meets";
const CODE: &str = "push_arm_code";
const SYMBOL: &str = "b3l_push";

/// The names of everything the theorem's statement rests on, sorted: read from the export itself.
fn rests_on(export: &Path, theorem: &str) -> Vec<String> {
    let id = |v: &Value| v.as_u64().expect("a number in the export") as usize;
    let mut names: Vec<String> = vec![String::new()];
    let mut kids: Vec<Vec<usize>> = Vec::new(); // an expression's parts
    let mut consts: Vec<Vec<usize>> = Vec::new(); // the constants it names itself
    let mut decl: HashMap<usize, (Vec<usize>, Vec<usize>)> = HashMap::new(); // a constant's expressions, and what comes with it
    fn put<T: Default + Clone>(v: &mut Vec<T>, i: usize, x: T) {
        if v.len() <= i {
            v.resize(i + 1, T::default());
        }
        v[i] = x;
    }
    for line in std::io::BufReader::new(std::fs::File::open(export).unwrap()).lines() {
        let o: Value = serde_json::from_str(&line.unwrap()).expect("a line of the export is JSON");
        if let Some(i) = o.get("in") {
            let (pre, s) = match (o.get("str"), o.get("num")) {
                (Some(s), _) => (id(&s["pre"]), s["str"].as_str().unwrap().to_string()),
                (_, Some(n)) => (id(&n["pre"]), n["i"].to_string()),
                _ => panic!("a name of an unknown kind"),
            };
            let full = if names[pre].is_empty() { s } else { format!("{}.{}", names[pre], s) };
            put(&mut names, id(i), full);
        } else if let Some(i) = o.get("ie") {
            let (mut k, mut c) = (Vec::new(), Vec::new());
            if let Some(x) = o.get("app") {
                k = vec![id(&x["fn"]), id(&x["arg"])];
            } else if let Some(x) = o.get("lam").or(o.get("forallE")) {
                k = vec![id(&x["type"]), id(&x["body"])];
            } else if let Some(x) = o.get("letE") {
                k = vec![id(&x["type"]), id(&x["value"]), id(&x["body"])];
            } else if let Some(x) = o.get("proj") {
                k = vec![id(&x["struct"])];
                c = vec![id(&x["typeName"])];
            } else if let Some(x) = o.get("mdata") {
                k = vec![id(&x["expr"])];
            } else if let Some(x) = o.get("const") {
                c = vec![id(&x["name"])];
            }
            put(&mut kids, id(i), k);
            put(&mut consts, id(i), c);
        } else if let Some(x) = o.get("def") {
            decl.insert(id(&x["name"]), (vec![id(&x["type"]), id(&x["value"])], vec![]));
        } else if let Some(x) = o.get("axiom").or(o.get("opaque")).or(o.get("thm")).or(o.get("quot")) {
            decl.insert(id(&x["name"]), (vec![id(&x["type"])], vec![])); // no proof, and no hidden body, is followed
        } else if let Some(b) = o.get("inductive") {
            let (mut members, mut exprs) = (Vec::new(), Vec::new());
            for part in ["types", "ctors", "recs"] {
                for x in b[part].as_array().unwrap() {
                    members.push(id(&x["name"]));
                    exprs.push(id(&x["type"]));
                    for rule in x.get("rules").and_then(|r| r.as_array()).into_iter().flatten() {
                        exprs.push(id(&rule["rhs"]));
                    }
                }
            }
            for m in &members {
                decl.insert(*m, (exprs.clone(), members.clone()));
            }
        } else {
            // a universe level, or the first line: neither names a constant
            assert!(o.get("il").is_some() || o.get("meta").is_some(), "a line of the export of an unknown kind: {o}");
        }
    }
    let start = names.iter().position(|n| n == theorem).expect("the theorem is in the export");
    let (mut seen_e, mut seen, mut todo) = (HashSet::new(), HashSet::new(), Vec::new());
    let mut of_expr = |root: usize, todo: &mut Vec<usize>| {
        let mut stack = vec![root];
        while let Some(e) = stack.pop() {
            if seen_e.insert(e) {
                todo.extend(&consts[e]);
                stack.extend(&kids[e]);
            }
        }
    };
    of_expr(decl[&start].0[0], &mut todo);
    while let Some(c) = todo.pop() {
        if seen.insert(c) {
            let (exprs, members) = decl.get(&c).unwrap_or_else(|| panic!("`{}` is named and not declared", names[c]));
            todo.extend(members);
            for e in exprs {
                of_expr(*e, &mut todo);
            }
        }
    }
    let mut out: Vec<String> = seen.into_iter().map(|c| names[c].clone()).collect();
    out.sort();
    out
}

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

    // What the statement rests on, found here from the export.
    let t_closure = Instant::now();
    let rests = rests_on(&export, THEOREM);
    assert!(rests.iter().any(|n| n == CODE), "the statement names the code");
    let closure = t_closure.elapsed();

    // 1. Every declaration checks; only Lean's three axioms are allowed.
    let printed = out.join("checked.txt");
    std::fs::File::create(&printed).unwrap();
    let config = out.join("checker.json");
    let mut print: Vec<&str> = vec![THEOREM];
    print.extend(rests.iter().map(|s| s.as_str()));
    std::fs::write(
        &config,
        serde_json::json!({
            "export_file_path": export, "use_stdin": false, "num_threads": 4,
            "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
            "pp_declars": print, "pp_to_stdout": false, "pp_output_path": printed,
            "pp_options": {"proofs": false, "width": 110}, "print_success_message": false
        })
        .to_string(),
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

    // 2. What was checked is what was read: the statement, and every definition it rests on.
    let text = std::fs::read_to_string(&printed).unwrap();
    assert!(errors.is_empty(), "the checker could not print: {errors:?}");
    let read_all = std::fs::read_to_string("proof/push_arm_meets.checked.txt").expect("the definitions to read");
    if text != read_all {
        let at = text.bytes().zip(read_all.bytes()).position(|(a, b)| a != b).unwrap_or(text.len().min(read_all.len()));
        let line = text[..at].matches('\n').count() + 1;
        let from = text[..at].rfind("\n\n").map_or(0, |i| i + 2);
        panic!(
            "what checks is not what is in proof/push_arm_meets.checked.txt: they part at line {line}, in:\n{}",
            text[from..].split("\n\n").next().unwrap().lines().take(6).collect::<Vec<_>>().join("\n")
        );
    }
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
        "cargo:warning=proof checked: {declarations} declarations in {:.1} s (unpacked in {:.1} s; what the statement rests on, {} constants, found in {:.1} s and compared with the text read); {} instruction words linked from the theorem",
        checked.as_secs_f64(),
        unpacked.as_secs_f64(),
        rests.len(),
        closure.as_secs_f64(),
        words.len()
    );
}
