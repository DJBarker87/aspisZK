use super::*;
static mut NBZ_Q:usize=1;
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.is_some());let _=phase;}
#[kani::proof] #[kani::unwind(8)]
fn NBZ_return_carriers(){unsafe{NBZ_Q=2;} NBZ_mark_none(None,Phase::Query(1));}
