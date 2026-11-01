use super::*;
static NBZ_Q:std::sync::atomic::AtomicUsize=std::sync::atomic::AtomicUsize::new(0);
fn NBZ_mark_none(obs:usize,phase:Phase) {
 assert!(obs==1);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 NBZ_Q.store(1,std::sync::atomic::Ordering::SeqCst);
 NBZ_mark_none(0,Phase::Query(1));
}
