#[path = "../src/vectors.rs"]
#[allow(dead_code)]
mod vectors;

fn main() {
    blake3::initialize();
    // The trailing newline is included.
    print!("{}", vectors::generate_json());
}
