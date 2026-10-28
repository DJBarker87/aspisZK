// Std-only diagnostic; no keys, input files or network. Run with core dumps off.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, Ordering};
struct Deny69;
static DENY: AtomicBool = AtomicBool::new(false);
unsafe impl GlobalAlloc for Deny69 {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if DENY.load(Ordering::Relaxed) && l.size() == 69 {
            std::ptr::null_mut()
        } else { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { System.dealloc(p,l) }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if DENY.load(Ordering::Relaxed) && n == 69 {
            std::ptr::null_mut()
        } else { System.realloc(p,l,n) }
    }
}
#[global_allocator] static ALLOCATOR: Deny69 = Deny69;
fn main() {
    let mode = std::env::args().nth(1).unwrap();
    DENY.store(true, Ordering::Relaxed);
    let s = if mode == "native" { String::with_capacity(69) }
            else { String::new() };
    std::hint::black_box(s);
    DENY.store(false, Ordering::Relaxed);
    println!("returned");
}
