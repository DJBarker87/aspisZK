use super::*;
static NBZ_Q:std::sync::atomic::AtomicUsize=std::sync::atomic::AtomicUsize::new(0);
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase) {
 assert!(obs.is_some());
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 NBZ_Q.store(1,std::sync::atomic::Ordering::SeqCst);
 NBZ_mark_none(None,Phase::Query(1));
}
