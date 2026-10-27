//! Returning allocation outcomes remain the existing Allocator boundary.
//! This probes actual helper error mapping with CBMC malloc-failure mode.
use aspis_core::field::QM31;
type Claims=[[QM31;29];3];
#[kani::proof] #[kani::unwind(32)]
fn NP6_uninit_allocation_outcomes(){
 let result=aspis_core::r0::heap::uninit::<Claims>();
 kani::cover!(result.is_ok(),"native helper returns an owned MaybeUninit box");
 kani::cover!(matches!(result,Err(aspis_core::r0::Error::Allocation)),"native helper propagates allocation failure");
}
#[kani::proof] #[kani::unwind(32)]
fn NP6_filled_allocation_outcomes(){
 let result=aspis_core::r0::heap::filled(3,[QM31::ZERO;29]);
 kani::cover!(result.is_ok(),"safe helper returns three initialized rows");
 kani::cover!(matches!(result,Err(aspis_core::r0::Error::Allocation)),"safe helper propagates allocation failure");
}
