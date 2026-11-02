//! Bounded host work on independent public inputs; source-order merge.
extern crate std;
use alloc::vec::Vec;
use core::cell::Cell;
std::thread_local! {static ACTIVE: Cell<bool> = const { Cell::new(false) };}
pub const THREADS: usize = 16;
/// Partition [0,n) into 16 adjacent ranges, in increasing source order.
pub fn range(n: usize, k: usize) -> (usize, usize) {
    assert!(k < THREADS);
    let q = n / THREADS;
    let r = n % THREADS;
    let start = q * k + core::cmp::min(k,r);
    (start, start + q + (k < r) as usize)
}
pub fn is_worker() -> bool { ACTIVE.with(Cell::get) }
struct Active(bool);
impl Active {
    fn enter() -> Self { Self(ACTIVE.with(|a| a.replace(true))) }
}
impl Drop for Active {fn drop(&mut self){ACTIVE.with(|a| a.set(self.0));}}
/// No nested teams; at most 15 spawned workers plus this calling thread.
/// Each range catches its panic, all handles are joined, then the first
/// source-order panic is resumed for the enclosing panic-to-reject boundary.
pub fn ordered_map<T: Send, F: Fn(usize) -> T + Sync>(n: usize, f: F) -> Vec<T> {
    ordered_map_inner(n,f,false)
}
pub fn ordered_families<T: Send, F: Fn(usize)->T + Sync>(n:usize,f:F)->Vec<T> {
    ordered_map_inner(n,f,true)
}
fn ordered_map_inner<T: Send,F: Fn(usize)->T+Sync>(n:usize,f:F,force:bool)->Vec<T> {
    if (n < THREADS*2 && !force) || is_worker() { return (0..n).map(f).collect(); }
    let _active = Active::enter();
    let run = |k| {
            let _active = Active::enter();
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let (a,b) = range(n,k);
                (a..b).map(&f).collect::<Vec<T>>()
            }))
    };
    let chunks = std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for k in 1..THREADS { let run = &run; handles.push(scope.spawn(move || run(k))); }
        let first = run(0);
        let mut chunks = Vec::with_capacity(THREADS);
        chunks.push(first);
        for handle in handles {
            chunks.push(match handle.join() {Ok(v)=>v,Err(p)=>Err(p)});
        }
        chunks
    });
    let mut out = Vec::with_capacity(n);
    for chunk in chunks {
        match chunk {Ok(mut v)=>out.append(&mut v),Err(p)=>std::panic::resume_unwind(p)}
    }
    out
}
