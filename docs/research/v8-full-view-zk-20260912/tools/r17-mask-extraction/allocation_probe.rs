//! Finite actual-source allocation/failure diagnostic, NOT a privacy proof.
//! Compile beside the pinned field.rs and r17_structured_g.rs, without tests.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub mod corelib {
    pub use crate::field;
}
mod r17_structured_g;

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

static ARMED: AtomicBool = AtomicBool::new(false);
static COUNT: AtomicUsize = AtomicUsize::new(0);
static FAIL_AT: AtomicUsize = AtomicUsize::new(0);
static SIZES: [AtomicUsize; 300] = [const { AtomicUsize::new(0) }; 300];
static ALIGNS: [AtomicUsize; 300] = [const { AtomicUsize::new(0) }; 300];
static KINDS: [AtomicUsize; 300] = [const { AtomicUsize::new(0) }; 300];

fn deny(size: usize, align: usize, kind: usize) -> bool {
    if !ARMED.load(SeqCst) {
        return false;
    }
    let i = COUNT.fetch_add(1, SeqCst);
    if i < SIZES.len() {
        SIZES[i].store(size, SeqCst);
        ALIGNS[i].store(align, SeqCst);
        KINDS[i].store(kind, SeqCst);
    }
    FAIL_AT.load(SeqCst) == i + 1
}

struct ProbeAllocator;
unsafe impl GlobalAlloc for ProbeAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if deny(layout.size(), layout.align(), 1) { std::ptr::null_mut() }
        else { unsafe { System.alloc(layout) } }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if deny(layout.size(), layout.align(), 2) { std::ptr::null_mut() }
        else { unsafe { System.alloc_zeroed(layout) } }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if deny(size, layout.align(), 3) { std::ptr::null_mut() }
        else { unsafe { System.realloc(ptr, layout, size) } }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: ProbeAllocator = ProbeAllocator;

fn main() {
    use field::{CM31, M31, QM31};
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 4, "mode point-tag fail-at");
    let mode = &args[1];
    let tag: u32 = args[2].parse().unwrap();
    let fail: usize = args[3].parse().unwrap();
    assert!(tag <= 1);
    assert!(mode == "row" || mode == "mask");
    let point = core::array::from_fn(|i| {
        let x = tag * 101 + i as u32;
        QM31 { c0: CM31::new(M31(x + 1), M31(x + 2)),
               c1: CM31::new(M31(x + 3), M31(x + 4)) }
    });
    FAIL_AT.store(fail, SeqCst);
    // No logging, environment parsing or dynamic diagnostic storage while armed.
    ARMED.store(true, SeqCst);
    let out = if mode == "row" {
        r17_structured_g::mixing_row(std::hint::black_box(tag as usize))
    } else {
        r17_structured_g::mask_weights(std::hint::black_box(&point))
    };
    std::hint::black_box(&out);
    ARMED.store(false, SeqCst);
    let count = COUNT.load(SeqCst);
    assert!(count <= SIZES.len(), "diagnostic event buffer overflow");
    assert_eq!(out.len(), r17_structured_g::N);
    println!("mode={mode} tag={tag} len={} allocations={count}", out.len());
    for i in 0..count {
        println!("{} {} {} {}", i + 1, SIZES[i].load(SeqCst),
                 ALIGNS[i].load(SeqCst), KINDS[i].load(SeqCst));
    }
}
