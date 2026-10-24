//! The C API (`b3.h`): a thin layer over the `blake3-servil` crate, its
//! contracts checked at the boundary (a panic here stops the program, as
//! every `extern "C"` panic does). Each call initializes the crate first
//! (a load once it has).

use blake3_servil::{Hash, Hasher, Mode, OUT_LEN, Stream};
use core::ffi::{CStr, c_char, c_void};

/// `b3_digest`.
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Digest {
    pub bytes: [u8; OUT_LEN],
}

/// `b3_mode`: `kind` 0 plain, 1 keyed (`key` the key), 2 key derivation
/// (`key` the hashed context).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct B3Mode {
    kind: u8,
    key: [u8; 32],
}

/// `b3_hasher`: the caller's memory, holding a `Hasher`.
#[repr(C, align(64))]
pub struct B3Hasher {
    opaque: [u8; HASHER_SIZE],
}

const HASHER_SIZE: usize = 18432;
const _: () = assert!(size_of::<Hasher>() == HASHER_SIZE && align_of::<Hasher>() <= 64, "b3.h's B3_HASHER_SIZE and alignment hold a Hasher");

impl B3Mode {
    fn mode(&self) -> Mode<'_> {
        match self.kind {
            0 => Mode::Hash,
            1 => Mode::Keyed(&self.key),
            2 => Mode::DeriveKeyMaterial(&self.key),
            kind => panic!("b3: a b3_mode made by b3_plain, b3_keyed, or b3_derive_key (kind {kind})"),
        }
    }
}

fn digest(hash: Hash) -> Digest {
    Digest { bytes: *hash.as_bytes() }
}

/// The bytes at `ptr`, `len` of them; NULL only with `len` 0.
unsafe fn bytes<'a>(ptr: *const c_void, len: usize, what: &str) -> &'a [u8] {
    if len == 0 {
        return &[];
    }
    assert!(!ptr.is_null(), "b3: {what} is NULL with a length of {len}");
    // Sound by the contract: `len` readable bytes at `ptr`.
    unsafe { core::slice::from_raw_parts(ptr as *const u8, len) }
}

unsafe fn mode<'a>(mode: *const B3Mode) -> &'a B3Mode {
    assert!(!mode.is_null(), "b3: the mode is NULL");
    unsafe { &*mode }
}

unsafe fn hasher<'a>(hasher: *const B3Hasher) -> &'a Hasher {
    assert!(!hasher.is_null(), "b3: the hasher is NULL");
    unsafe { &*(hasher as *const Hasher) }
}

unsafe fn hasher_mut<'a>(hasher: *mut B3Hasher) -> &'a mut Hasher {
    assert!(!hasher.is_null(), "b3: the hasher is NULL");
    unsafe { &mut *(hasher as *mut Hasher) }
}

/// `b3_version`: the library's version, as `b3.h`'s `B3_VERSION`.
#[unsafe(no_mangle)]
pub extern "C" fn b3_version() -> *const c_char {
    concat!(env!("CARGO_PKG_VERSION"), "\0").as_ptr().cast()
}

#[unsafe(no_mangle)]
pub extern "C" fn b3_plain() -> B3Mode {
    B3Mode { kind: 0, key: [0; 32] }
}

/// # Safety
/// `key` points at 32 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_keyed(key: *const u8) -> B3Mode {
    assert!(!key.is_null(), "b3: the key is NULL");
    B3Mode { kind: 1, key: unsafe { *(key as *const [u8; 32]) } }
}

/// # Safety
/// `context` is a NUL-terminated string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_derive_key(context: *const c_char) -> B3Mode {
    blake3_servil::initialize();
    assert!(!context.is_null(), "b3: the context is NULL");
    let context = unsafe { CStr::from_ptr(context) }.to_str().expect("b3: the context is UTF-8");
    B3Mode { kind: 2, key: blake3_servil::hash_derive_key_context(context) }
}

/// # Safety
/// `mode` is a mode; `input` holds `len` bytes (NULL only with `len` 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hash(mode: *const B3Mode, input: *const c_void, len: usize) -> Digest {
    blake3_servil::initialize();
    let mode = unsafe { self::mode(mode) };
    let mut out = blake3_servil::Hash::from([0; 32]);
    blake3_servil::hash_with(mode.mode(), unsafe { bytes(input, len, "the input") }, &mut out);
    digest(out)
}

/// # Safety
/// As `b3_hash`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hash_multithreaded(mode: *const B3Mode, input: *const c_void, len: usize) -> Digest {
    blake3_servil::initialize_multithreaded(None);
    let mode = unsafe { self::mode(mode) };
    let mut out = blake3_servil::Hash::from([0; 32]);
    blake3_servil::hash_multithreaded_with(mode.mode(), unsafe { bytes(input, len, "the input") }, &mut out);
    digest(out)
}

/// The batch's input and digests, as slices.
unsafe fn batch<'a>(input: *const c_void, message_len: usize, count: usize, out: *mut Digest) -> (&'a [u8], &'a mut [[u8; OUT_LEN]]) {
    let stride = if message_len == 0 { 64 } else { message_len.div_ceil(64) * 64 };
    let total = stride.checked_mul(count).expect("b3: the batch's length fits a size_t");
    let input = unsafe { bytes(input, total, "the batch") };
    if count == 0 {
        return (input, &mut []);
    }
    assert!(!out.is_null(), "b3: the digests are NULL with a count of {count}");
    // Sound by the contract: room for `count` digests at `out`; a Digest is
    // 32 bytes, as [u8; 32] is.
    (input, unsafe { core::slice::from_raw_parts_mut(out as *mut [u8; OUT_LEN], count) })
}

/// # Safety
/// `mode` is a mode; `input` holds `count` strides of `message_len`
/// (NULL only with `count` 0), the bytes past each message zero; `out`
/// has room for `count` digests.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hash_many(mode: *const B3Mode, input: *const c_void, message_len: usize, count: usize, out: *mut Digest) {
    blake3_servil::initialize();
    let mode = unsafe { self::mode(mode) };
    let (input, out) = unsafe { batch(input, message_len, count, out) };
    blake3_servil::hash_many_with(mode.mode(), input, message_len, out);
}

/// # Safety
/// As `b3_hash_many`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hash_many_multithreaded(mode: *const B3Mode, input: *const c_void, message_len: usize, count: usize, out: *mut Digest) {
    blake3_servil::initialize_multithreaded(None);
    let mode = unsafe { self::mode(mode) };
    let (input, out) = unsafe { batch(input, message_len, count, out) };
    blake3_servil::hash_many_multithreaded_with(mode.mode(), input, message_len, out);
}

/// # Safety
/// `hasher` points at a `b3_hasher`'s memory; `mode` is a mode.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hasher_init(hasher: *mut B3Hasher, mode: *const B3Mode) {
    blake3_servil::initialize();
    assert!(!hasher.is_null(), "b3: the hasher is NULL");
    let mode = unsafe { self::mode(mode) };
    let new = match mode.mode() {
        _ => Hasher::new_with(mode.mode()),
    };
    // Sound: the memory is the caller's, sized and aligned for a Hasher,
    // which owns nothing to drop.
    unsafe { (hasher as *mut Hasher).write(new) };
}

/// # Safety
/// `hasher` was initialized by `b3_hasher_init`; `input` holds `len`
/// bytes (NULL only with `len` 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hasher_update(hasher: *mut B3Hasher, input: *const c_void, len: usize) {
    let hasher = unsafe { hasher_mut(hasher) };
    hasher.update(unsafe { bytes(input, len, "the input") });
}

/// # Safety
/// As `b3_hasher_update`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hasher_update_multithreaded(hasher: *mut B3Hasher, input: *const c_void, len: usize) {
    blake3_servil::initialize_multithreaded(None);
    let hasher = unsafe { hasher_mut(hasher) };
    hasher.update_multithreaded(unsafe { bytes(input, len, "the input") });
}

/// # Safety
/// `hasher` was initialized by `b3_hasher_init`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hasher_finalize(hasher: *const B3Hasher) -> Digest {
    digest(unsafe { self::hasher(hasher) }.finalize())
}

/// # Safety
/// `hasher` was initialized by `b3_hasher_init`; `out` has room for `len`
/// bytes (NULL only with `len` 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_hasher_output(hasher: *const B3Hasher, offset: u64, out: *mut c_void, len: usize) {
    let hasher = unsafe { self::hasher(hasher) };
    if len == 0 {
        return;
    }
    assert!(!out.is_null(), "b3: the output is NULL with a length of {len}");
    let mut reader = hasher.finalize_xof();
    reader.set_position(offset);
    // Sound by the contract: room for `len` bytes at `out`.
    reader.fill(unsafe { core::slice::from_raw_parts_mut(out as *mut u8, len) });
}

/// The C handler: called with each place handed back, in order, on the
/// thread that made the stream's calls.
pub type B3Done = unsafe extern "C" fn(ctx: *mut c_void, places: *mut Digest, count: usize);

/// What the stream's handler is in Rust: the C function and its context.
type Done = Box<dyn FnMut(&'static mut [Hash])>;

/// `b3_stream`: a [`Stream`] the program holds between `b3_stream_begin`
/// and `b3_stream_finish`. The messages and places a C program submits
/// live as long as the stream (its contract), which `'static` stands for
/// here.
pub struct B3Stream {
    stream: Stream<'static, Done>,
    finished: bool,
}

unsafe fn stream_mut<'a>(stream: *mut B3Stream) -> &'a mut B3Stream {
    assert!(!stream.is_null(), "b3: the stream is NULL");
    let s = unsafe { &mut *stream };
    assert!(!s.finished, "b3: the stream is finished; begin another");
    s
}

/// # Safety
/// `mode` is a mode; `done` is a function; `ctx` is passed to it unread.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_stream_begin(mode: *const B3Mode, done: B3Done, ctx: *mut c_void) -> *mut B3Stream {
    blake3_servil::initialize_multithreaded(None);
    let mode = unsafe { self::mode(mode) };
    let ctx = ctx as usize;
    let handler: Done = Box::new(move |places: &mut [Hash]| {
        // Sound: a Hash is a Digest (both 32 bytes, repr(transparent)).
        unsafe { done(ctx as *mut c_void, places.as_mut_ptr() as *mut Digest, places.len()) }
    });
    Box::into_raw(Box::new(B3Stream { stream: Stream::open(mode.mode(), handler), finished: false }))
}

/// # Safety
/// `stream` came from `b3_stream_begin` and is not finished; `input` holds
/// `len` bytes (NULL only with `len` 0) and `out` a digest's room, both
/// alive until `b3_stream_finish`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_stream_submit(stream: *mut B3Stream, input: *const c_void, len: usize, out: *mut Digest) {
    let s = unsafe { stream_mut(stream) };
    assert!(!out.is_null(), "b3: the digest's place is NULL");
    // Sound by the contract: both live until finish, which is 'static to
    // the stream; a Digest is a Hash.
    let input: &'static [u8] = unsafe { bytes(input, len, "the input") };
    s.stream.submit(input, unsafe { &mut *(out as *mut Hash) });
}

/// # Safety
/// As `b3_stream_submit`, with `input` holding `count` strides of
/// `message_len` (NULL only with `count` 0) and `out` room for `count`
/// digests.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_stream_submit_batch(stream: *mut B3Stream, input: *const c_void, message_len: usize, count: usize, out: *mut Digest) {
    let s = unsafe { stream_mut(stream) };
    let (input, places) = unsafe { batch(input, message_len, count, out) };
    // Sound: the batch and its places live until finish; a [u8; 32] is a Hash.
    let input: &'static [u8] = unsafe { core::slice::from_raw_parts(input.as_ptr(), input.len()) };
    let places: &'static mut [Hash] = unsafe { core::slice::from_raw_parts_mut(places.as_mut_ptr() as *mut Hash, places.len()) };
    s.stream.submit_batch(input, message_len, places);
}

/// # Safety
/// `stream` came from `b3_stream_begin` and is not finished.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_stream_collect(stream: *mut B3Stream) {
    unsafe { stream_mut(stream) }.stream.collect();
}

/// # Safety
/// `stream` came from `b3_stream_begin` and is not finished. After this
/// call the stream is gone; its messages and places are the program's
/// again, every place handed back.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn b3_stream_finish(stream: *mut B3Stream) {
    let s = unsafe { stream_mut(stream) };
    s.stream.finish();
    s.finished = true;
    // Sound: made by Box::into_raw in b3_stream_begin, finished once.
    drop(unsafe { Box::from_raw(stream) });
}

#[cfg(test)]
mod test {
    include!("../../tools/require_nextest.rs");
}
