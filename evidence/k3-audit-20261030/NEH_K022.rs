use super::*;
static mut NBZ_Q:usize=0; static NBZ_UNWRITTEN:Option<core::num::NonZeroUsize>=None;
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.is_some());let _=phase;}
#[kani::proof] #[kani::unwind(8)]
fn NBZ_return_carriers(){unsafe{NBZ_Q=1;} assert!(NBZ_UNWRITTEN.is_some()); NBZ_mark_none(None,Phase::Query(1));}
