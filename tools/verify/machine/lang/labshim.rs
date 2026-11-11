
/// For the proof lab (BLAKE3 #361): the hasher's stack as the crate has it, for comparison with
/// functions written in Lean. Not part of the API.
#[doc(hidden)]
pub mod labshim {
    pub use crate::hasher::CvStack;
    pub fn new_stack() -> CvStack {
        CvStack::new()
    }
    pub fn push(stack: &mut CvStack, cv: [u8; 32]) {
        stack.push(cv)
    }
    pub fn clear(stack: &mut CvStack) {
        stack.clear()
    }
    pub fn len(stack: &CvStack) -> usize {
        stack.len()
    }
    pub fn get(stack: &CvStack, i: usize) -> [u8; 32] {
        stack.get(i)
    }
    #[inline(never)]
    pub fn merge(stack: &mut CvStack, key: &[u32; 8], flags: u8, target: usize) {
        let kernels = crate::hasher::Kernels { key, flags, platform: crate::platform::Platform::detect(), hooks: () };
        stack.merge(&kernels, target)
    }
    pub fn platform_number() -> u8 {
        crate::platform::Platform::detect() as u8
    }
}
