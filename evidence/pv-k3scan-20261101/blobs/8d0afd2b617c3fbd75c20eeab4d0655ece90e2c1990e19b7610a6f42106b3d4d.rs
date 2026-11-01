use aspis_core::field::{QM31,CM31,M31};
use crate::{host_copy_terminal::access16 as dcopy,reference_copy_terminal::access16 as rcopy,
 host_copy_terminal::access16 as unused};
fn q()->QM31 { let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}} }
fn qs<const N:usize>()->[QM31;N] { let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a }
fn frozen(m:u16)->bool { matches!(m,1749|2048|2049|4097|6144|6145|26214) }
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host() { let v=qs();let m:u16=kani::any();kani::assume(frozen(m));assert_eq!(dcopy::mask(&v,m),rcopy::mask(&v,m)); }
#[kani::proof] #[kani::unwind(70)]
fn selector_domain() { let masks=dcopy::masks();let b:usize=kani::any();kani::assume(b<64);assert!(masks[b]==0||frozen(masks[b])); }
