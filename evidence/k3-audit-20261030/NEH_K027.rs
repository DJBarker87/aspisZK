use super::*;
static mut NBZ_Q:Option<core::num::NonZeroUsize>=None;
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.is_some());let _=phase;}
#[kani::proof] #[kani::unwind(8)]
fn NBZ_return_carriers(){unsafe{NBZ_Q=core::num::NonZeroUsize::new(1);} NBZ_mark_none(None,Phase::Query(1));}
