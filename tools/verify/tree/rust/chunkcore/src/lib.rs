#![no_std]
//! A chunk's state (src/chunk_core.rs, included here as it is), for Aeneas:
//! its block length and start flag.

pub const BLOCK_LEN: usize = 64;
pub const CHUNK_START: u8 = 1;

include!("../../../../../../src/chunk_core.rs");
