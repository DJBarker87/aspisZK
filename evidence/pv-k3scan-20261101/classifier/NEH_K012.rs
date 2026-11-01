use super::*;

fn NBZ_mark_none(obs:usize,phase:Phase) {
 assert!(obs==1);
 let _=phase;
}
#[kani::proof]
#[kani::unwind(8)]
fn NBZ_return_carriers() {
 let mut record=0usize; record=1; assert!(record==1);
 NBZ_mark_none(0,Phase::Query(1));
}
