//! A child module of src/pipeline.rs under `--cfg shuttle` alone
//! (tests/shuttle_pipeline.rs): it reaches the Pipeline's private storage
//! list to free a run's storages at the run's end.

use super::{FREE_STORAGES, Ordering, PipeStorage, STORAGES_MADE};

/// At the end of one run of the model, every storage made in it is free
/// again (returned: how many made, how many free), and is freed here. A
/// program never frees one; a model that ran thousands of schedules
/// without freeing would hold them all, and Shuttle's atomics must not
/// pass from one run to the next.
pub(crate) fn free_storages_for_model() -> (usize, usize) {
    let free: Vec<&'static PipeStorage> = FREE_STORAGES.lock().unwrap().drain(..).collect();
    let made = STORAGES_MADE.swap(0, Ordering::SeqCst);
    let back = free.len();
    for st in free {
        // Sound: the model's threads have all ended, and nothing holds a
        // storage that is on the free list.
        unsafe {
            let shared = *st.shared.get();
            if !shared.is_null() {
                drop(Box::from_raw(shared));
            }
            let (at, len) = st.rooms.backing;
            if !at.is_null() {
                drop(Box::from_raw(core::ptr::slice_from_raw_parts_mut(at, len)));
            }
            drop(Box::from_raw(st as *const PipeStorage as *mut PipeStorage));
        }
    }
    (made, back)
}
