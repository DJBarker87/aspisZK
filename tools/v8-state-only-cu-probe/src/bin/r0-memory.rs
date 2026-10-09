//! Cumulative allocation model of Solana's non-freeing bump allocator.
use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst},
};
static ACTIVE: AtomicBool = AtomicBool::new(false);
static CURSOR: AtomicUsize = AtomicUsize::new(0);
struct Measured;
unsafe impl GlobalAlloc for Measured {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if ACTIVE.load(SeqCst) {
            CURSOR
                .fetch_update(SeqCst, SeqCst, |v| {
                    Some((v.saturating_sub(l.size())) & !(l.align() - 1))
                })
                .unwrap();
        }
        System.alloc(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l)
    }
}
#[global_allocator]
static ALLOC: Measured = Measured;
fn main() {
    assert!(!cfg!(debug_assertions));
    let args: Vec<_> = std::env::args().collect();
    let dir = std::path::Path::new(&args[1]);
    let mut records = Vec::new();
    for name in ["transfer", "withdrawal"] {
        let proof = std::fs::read(dir.join(format!("{name}.proof.bin"))).unwrap();
        let public = std::fs::read(dir.join(format!("{name}.public.bin"))).unwrap();
        let public =
            aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public)
                .unwrap();
        CURSOR.store(256 * 1024, SeqCst);
        ACTIVE.store(true, SeqCst);
        let result = aspis_statement::r0::r0_verify(
            aspis_prover::r0_fixture::statement_public(&public),
            &proof,
            aspis_prover::HOST_HASH,
            None,
        );
        ACTIVE.store(false, SeqCst);
        let used = 256 * 1024 - CURSOR.load(SeqCst);
        assert!(result.is_ok(), "{name}: {result:?}");
        records.push(serde_json::json!({"variant":name,"verifier_cumulative_heap_bytes":used,"allocator_cursor_bytes":8,"accepted":true}));
        assert!(used + 8 <= 256 * 1024, "heap stop: {used}");
    }
    std::fs::write(&args[2], serde_json::to_vec_pretty(&records).unwrap()).unwrap();
}
