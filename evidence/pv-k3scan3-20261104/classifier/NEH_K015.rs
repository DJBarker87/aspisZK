use super::*;
static mut NBZ_Q:usize=0x0101010101010101;
fn NBZ_mark_none(obs:[u8;8],phase:Phase) {
 assert!(obs[0]==2);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 unsafe{NBZ_Q=0x0202020202020202;}
 NBZ_mark_none([1;8],Phase::Query(1));
}
