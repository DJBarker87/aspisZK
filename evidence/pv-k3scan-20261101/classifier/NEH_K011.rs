use super::*;
static NBZ_Q:usize=0;
fn NBZ_mark_none(obs:usize,phase:Phase) {
 assert!(obs==1);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 let _read=NBZ_Q;
 NBZ_mark_none(0,Phase::Query(1));
}
