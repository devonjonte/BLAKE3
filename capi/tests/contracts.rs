//! Every contract the C API checks: a call that breaks it stops the
//! program, with the contract's words on stderr. Each broken call runs in a
//! child process (this test binary again, running `broken_call`), since a
//! panic cannot unwind out of an `extern "C"` function: the process aborts,
//! as the header promises.

#![cfg(unix)]

use b3_servil::*;
use core::ffi::{c_char, c_void};
use std::os::unix::process::ExitStatusExt;

extern "C" fn ignore(_: *mut c_void, _: *mut Digest, _: usize) {}

/// 64 bytes on a 64-byte boundary, and the address one byte past it.
#[repr(C, align(64))]
struct Aligned([u8; 128]);

/// The broken calls, each named with the words its stop says.
const CASES: &[(&str, &str)] = &[
    ("input NULL", "b3: the input is NULL with a length of 5"),
    ("mode NULL", "b3: the mode is NULL"),
    ("mode unmade", "b3: a b3_mode made by b3_plain, b3_keyed, or b3_derive_key (kind 9)"),
    ("key NULL", "b3: the key is NULL"),
    ("context NULL", "b3: the context is NULL"),
    ("context not UTF-8", "b3: the context is UTF-8"),
    ("batch misplaced", "b3: a batch starts at a 64-byte boundary"),
    ("batch NULL", "b3: the batch is NULL with a length of 128"),
    ("batch too long", "b3: the batch's length fits a size_t"),
    ("digests NULL", "b3: the digests are NULL with a count of 2"),
    ("hasher NULL", "b3: the hasher is NULL"),
    ("output NULL", "b3: the output is NULL with a length of 5"),
    ("stream NULL", "b3: the stream is NULL"),
    ("place NULL", "b3: the digest's place is NULL"),
    ("stream input NULL", "b3: the input is NULL with a length of 3"),
    ("message misplaced", "b3: a submitted message starts at a 64-byte boundary"),
];

/// The broken call named in B3_BROKEN; with none named, nothing (as when
/// the suite runs this test itself).
#[test]
fn broken_call() {
    let Ok(case) = std::env::var("B3_BROKEN") else { return };
    let mode = b3_plain();
    let mut block = Aligned([0; 128]);
    let at = block.0.as_mut_ptr() as *mut c_void;
    let misplaced = unsafe { block.0.as_ptr().add(1) } as *const c_void;
    let mut out = [Digest { bytes: [0; 32] }; 2];
    unsafe {
        match case.as_str() {
            "input NULL" => {
                core::hint::black_box(b3_hash(&mode, core::ptr::null(), 5));
            }
            "mode NULL" => {
                core::hint::black_box(b3_hash(core::ptr::null(), at, 5));
            }
            "mode unmade" => {
                let mut unmade = b3_plain();
                // A mode's fields are the library's; kind 9 is none it makes.
                *(&mut unmade as *mut B3Mode as *mut u8) = 9;
                core::hint::black_box(b3_hash(&unmade, at, 5));
            }
            "key NULL" => {
                core::hint::black_box(b3_keyed(core::ptr::null()));
            }
            "context NULL" => {
                core::hint::black_box(b3_derive_key(core::ptr::null()));
            }
            "context not UTF-8" => {
                core::hint::black_box(b3_derive_key(b"\xff\0".as_ptr() as *const c_char));
            }
            "batch misplaced" => b3_hash_many(&mode, misplaced, 64, 1, out.as_mut_ptr()),
            "batch NULL" => b3_hash_many(&mode, core::ptr::null(), 64, 2, out.as_mut_ptr()),
            "batch too long" => b3_hash_many(&mode, at, 64, usize::MAX / 32, out.as_mut_ptr()),
            "digests NULL" => b3_hash_many(&mode, at, 1, 2, core::ptr::null_mut()),
            "hasher NULL" => b3_hasher_update(core::ptr::null_mut(), at, 5),
            "output NULL" => {
                let mut hasher: Box<B3Hasher> = Box::new(core::mem::zeroed());
                b3_hasher_init(&mut *hasher, &mode);
                b3_hasher_output(&*hasher, 0, core::ptr::null_mut(), 5)
            }
            "stream NULL" => b3_stream_submit(core::ptr::null_mut(), at, 5, out.as_mut_ptr()),
            "place NULL" => b3_stream_submit(b3_stream_begin(&mode, ignore, core::ptr::null_mut()), at, 5, core::ptr::null_mut()),
            "stream input NULL" => b3_stream_submit(b3_stream_begin(&mode, ignore, core::ptr::null_mut()), core::ptr::null(), 3, out.as_mut_ptr()),
            "message misplaced" => b3_stream_submit(b3_stream_begin(&mode, ignore, core::ptr::null_mut()), misplaced, 5, out.as_mut_ptr()),
            other => panic!("no broken call named {other:?}"),
        }
    }
    unreachable!("{case}: the call returned, its contract broken");
}

#[test]
fn every_broken_contract_stops_the_program() {
    let exe = std::env::current_exe().unwrap();
    for (case, words) in CASES {
        let child = std::process::Command::new(&exe).args(["broken_call", "--exact", "--nocapture"]).env("B3_BROKEN", case).output().unwrap();
        let stderr = String::from_utf8_lossy(&child.stderr);
        assert_eq!(child.status.signal(), Some(libc::SIGABRT), "{case}: the process aborts ({:?}); stderr:\n{stderr}", child.status);
        assert!(stderr.contains(words), "{case}: stderr says {words:?}:\n{stderr}");
    }
}
