//! Fixed public work ranges; no operand-dependent work stealing or cancellation.
use alloc::vec::Vec;
#[path="../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod pool;
#[cfg(feature="public-work-trace")]
static TRACE: std::sync::Mutex<Vec<[usize;6]>> = std::sync::Mutex::new(Vec::new());
/// Only public stage/shape/range and completed callback counts, never operands.
#[cfg(feature="public-work-trace")]
pub fn take_trace() -> Vec<[usize;6]> { core::mem::take(&mut *TRACE.lock().unwrap()) }
pub(crate) fn map<T:Send,F:Fn(usize)->T+Sync>(_stage:usize,n:usize,f:F)->Vec<T> {
    let chunks=pool::ordered_families(pool::THREADS,|k| {
        let (a,b)=pool::range(n,k);
        let mut out=Vec::with_capacity(b-a);
        let mut completed=0;
        for i in a..b {out.push(f(i));completed+=1;}
        (out,completed)
    });
    let mut out=Vec::with_capacity(n);
    for (k,(mut chunk,completed)) in chunks.into_iter().enumerate() {
        #[cfg(feature="public-work-trace")]
        {let (a,b)=pool::range(n,k);TRACE.lock().unwrap().push([_stage,n,k,a,b,completed]);}
        #[cfg(not(feature="public-work-trace"))]
        let _=(k,completed);
        out.append(&mut chunk);
    }
    out
}
