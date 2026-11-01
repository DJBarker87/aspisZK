use super::*;
static mut NBZ_Q:usize=1;
fn NBZ_mark_none(obs:usize,phase:Phase) {
 assert!(obs==2);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 unsafe{NBZ_Q=2;}
 NBZ_mark_none(1,Phase::Query(1));
}
