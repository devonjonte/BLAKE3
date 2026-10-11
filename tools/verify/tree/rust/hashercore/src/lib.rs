#![no_std]
//! The Hasher's stack, loop, and chunk state (src/stack_core.rs,
//! src/hasher_core.rs, src/chunk_core.rs, included here as they are), for
//! Aeneas: their constants and chaining-value type.

pub type Cv = [u8; 32];
pub const DEPTH: usize = 55;
pub const CHUNK_LEN: usize = 1024;
pub const BLOCK_LEN: usize = 64;
pub const CHUNK_START: u8 = 1;

include!("../../../../../../src/stack_core.rs");
include!("../../../../../../src/hasher_core.rs");
include!("../../../../../../src/chunk_core.rs");
