#![no_std]
//! The Hasher's stack and loop (src/stack_core.rs and src/hasher_core.rs,
//! included here as they are), for Aeneas: their chaining-value type,
//! depth, and chunk length.

pub type Cv = [u8; 32];
pub const DEPTH: usize = 55;
pub const CHUNK_LEN: usize = 1024;

include!("../../../../../../src/stack_core.rs");
include!("../../../../../../src/hasher_core.rs");
