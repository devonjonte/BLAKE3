#!/usr/bin/env python3
"""Check the real WakerSlot publication on Apple arm64 (#463).

Shuttle checks schedules under SC; it cannot detect the missing barrier
between the registration store and an RCpc completion re-check. Compile
waker.rs with its production atomic primitives, then remove just the
fence in a scratch copy to check that this test distinguishes the two.
No target linker or hardware is needed.
"""
from pathlib import Path
import re
import subprocess
import tempfile


PROBE = """
#![allow(dead_code, unused_imports)]
mod waker_sync {
    pub use core::cell::UnsafeCell;
    pub use core::sync::atomic::{AtomicUsize, Ordering, fence};
    #[inline(always)]
    pub fn spin() { core::hint::spin_loop(); }
    #[inline(always)]
    pub unsafe fn with_mut<T, R>(cell: &UnsafeCell<T>, f: impl FnOnce(&mut T) -> R) -> R {
        f(unsafe { &mut *cell.get() })
    }
}
mod waker;

#[unsafe(no_mangle)]
pub(crate) fn register_then_recheck(
    slot: &waker::WakerSlot,
    cx: &core::task::Context<'_>,
    completed: &core::sync::atomic::AtomicUsize,
) -> usize {
    slot.register(cx);
    completed.load(core::sync::atomic::Ordering::Acquire)
}
"""


def ordered(waker, directory):
    (directory / "waker.rs").write_text(waker)
    asm = directory / "probe.s"
    subprocess.run([
        "rustc", "--edition", "2024", "--crate-type", "lib", "-O", "-C", "panic=abort",
        "--target", "aarch64-apple-darwin", "--emit", "asm", "-o", str(asm),
        str(directory / "probe.rs"),
    ], check=True)
    body = asm.read_text().split("\n_register_then_recheck:\n", 1)[1].split(".cfi_endproc", 1)[0]
    # This probe inlines register; the release-store publishes REGISTERED
    # and the RCpc acquire-load reads completion. Fail rather than silently
    # credit a different compiler sequence or a fence in another function.
    stores = list(re.finditer(r"^[ \t]+stlr\b[^\n]*\n", body, re.M))
    loads = list(re.finditer(r"^[ \t]+ldapr\b", body, re.M))
    if len(stores) != 1 or len(loads) != 1 or stores[0].end() > loads[0].start():
        raise SystemExit("waker ordering: no unique stlr/ldapr pair in the Apple arm64 probe")
    between = body[stores[0].end():loads[0].start()]
    return re.match(r"[ \t]+dmb[ \t]+ish[ \t]*\n", between) is not None


def main():
    source = (Path(__file__).resolve().parents[1] / "threads/src/waker.rs").read_text()
    fence = "fence(Ordering::SeqCst);"
    if source.count(fence) != 1:
        raise SystemExit("waker ordering: expected one SeqCst fence in waker.rs")
    with tempfile.TemporaryDirectory(prefix="waker-order-") as tmp:
        directory = Path(tmp)
        (directory / "probe.rs").write_text(PROBE)
        if not ordered(source, directory):
            raise SystemExit("waker ordering: missing dmb ish after register's stlr")
        if ordered(source.replace(fence, ""), directory):
            raise SystemExit("waker ordering: removing the fence did not remove the barrier")
    print("waker ordering: Apple arm64 stlr/dmb ish/ldapr; unfenced control rejected")


if __name__ == "__main__":
    main()
