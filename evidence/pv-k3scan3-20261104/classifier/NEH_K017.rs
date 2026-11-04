use super::*;
static NBZ_Q:usize=0;
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase) {
 assert!(obs.is_some());
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 let _read=NBZ_Q;
 NBZ_mark_none(None,Phase::Query(1));
}
