use super::{Observer, Phase};
#[inline(never)]
fn KNB_check(obs: Observer, phase: Phase) {
    assert!(obs.is_none());
    match phase { Phase::Query(i) => assert!(i < 10), _ => panic!("wrong phase") }
}
fn KNB_case() {
    let i: usize = kani::any();
    kani::assume(i < 10);
    KNB_check(None, Phase::Query(i));
}
#[kani::proof]
#[kani::unwind(4096)]
fn KNB_none_query() { KNB_case() }
#[kani::proof]
#[kani::unwind(64)]
fn KNB_none_query64() { KNB_case() }
