use super::*;
struct Wrap(core::cell::UnsafeCell<usize>);unsafe impl Sync for Wrap {} static NBZ_Q:Wrap=Wrap(core::cell::UnsafeCell::new(0));
fn NBZ_mark_none(obs:Option<core::num::NonZeroUsize>,phase:Phase){assert!(obs.is_some());let _=phase;}
#[kani::proof] #[kani::unwind(8)]
fn NBZ_return_carriers(){unsafe{*NBZ_Q.0.get()=1;} NBZ_mark_none(None,Phase::Query(1));}
