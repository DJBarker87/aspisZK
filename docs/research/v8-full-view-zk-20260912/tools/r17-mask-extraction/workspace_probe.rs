//! Actual-source differential/allocation-denial controls, not a formal proof.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub mod corelib { pub use crate::field; }
mod r17_structured_g;
mod r17_mask_workspace;

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};
static ARMED: AtomicBool = AtomicBool::new(false);
static CALLS: AtomicUsize = AtomicUsize::new(0);
struct DenyWhileArmed;
fn denied() -> bool {
    if ARMED.load(SeqCst) { CALLS.fetch_add(1, SeqCst); true } else { false }
}
unsafe impl GlobalAlloc for DenyWhileArmed {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if denied() { std::ptr::null_mut() } else { unsafe { System.alloc(l) } }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if denied() { std::ptr::null_mut() } else { unsafe { System.alloc_zeroed(l) } }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if denied() { std::ptr::null_mut() } else { unsafe { System.realloc(p, l, n) } }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { unsafe { System.dealloc(p, l) } }
}
#[global_allocator]
static ALLOCATOR: DenyWhileArmed = DenyWhileArmed;

fn main() {
    use field::{CM31, M31, QM31 as K};
    use r17_structured_g::{COINS, N, ROUNDS};
    let mut coins = [K::ONE; COINS];
    let mut weights = [K::ONE; N];
    for case in 0..16u32 {
        let point: [K; ROUNDS] = core::array::from_fn(|j| {
            if case == 0 { return K::ZERO; }
            if case == 1 { return K::ONE; }
            let word = |k: u32| if case == 2 { M31(2147483646) }
                else { M31((case * 104729 + j as u32 * 8191 + k * 65537) % 2147483647) };
            K { c0: CM31::new(word(0), word(1)), c1: CM31::new(word(2), word(3)) }
        });
        let expected = r17_structured_g::mask_weights(&point);
        // Reuse dirty buffers. The candidate must overwrite every coordinate.
        ARMED.store(true, SeqCst);
        r17_mask_workspace::mask_weights_into(std::hint::black_box(&point), &mut coins, &mut weights);
        std::hint::black_box(&weights);
        ARMED.store(false, SeqCst);
        assert_eq!(CALLS.load(SeqCst), 0);
        assert_eq!(weights.as_slice(), expected.as_slice(), "case {case}");
    }
    println!("PASS: 16 canonical point arrays, all 1024 coordinates, dirty buffers, zero allocation attempts");
}
