use super::*;
static mut NBZ_Q:usize=0;
fn NBZ_mark_none(obs:u8,phase:Phase) {
 assert!(obs==1);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 unsafe{NBZ_Q=1;}
 NBZ_mark_none(0,Phase::Query(1));
}
