use super::*;
pub(super) fn reference(page:&RootHistoryPageV1)->bool { page.filled==256 }
#[cfg(kani)]
#[kani::proof_for_contract(RootHistoryPageV1::is_full)]
fn small_contract(){let p:RootHistoryPageV1=kani::any();let _=p.is_full();}
