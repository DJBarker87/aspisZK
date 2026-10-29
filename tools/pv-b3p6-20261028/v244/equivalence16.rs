use aspis_core::field::{QM31,CM31,M31};
use crate::{host_copy_terminal::access16 as dcopy,reference_copy_terminal::access16 as rcopy,
 host_terminal::access16 as dep,reference_terminal::access16 as reference};
fn q()->QM31 { let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}} }
fn qs<const N:usize>()->[QM31;N] { let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a }
fn frozen(m:u16)->bool { matches!(m,1749|2048|2049|4097|6144|6145|26214) }
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host() { let v=qs();let m:u16=kani::any();kani::assume(frozen(m));assert_eq!(dcopy::mask(&v,m),rcopy::mask(&v,m)); }
#[kani::proof] #[kani::unwind(70)]
fn selector_domain() { let masks=dcopy::masks();let b:usize=kani::any();kani::assume(b<64);assert!(masks[b]==0||frozen(masks[b])); }
// The second deployed source body is token-identical; see CLASSIFY.json. Its
// whole module is not in this crate: no separate source-binding credit is claimed.
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn reconstruct_10() {let v=qs();assert_eq!(dep::reconstruct(&v),reference::reconstruct(&v));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn equality_value() {let a=qs();let b=qs();assert_eq!(dep::equality(&a,&b),reference::equality(&a,&b));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high() { let h=qs();let l=qs();let a:usize=kani::any();let b:usize=kani::any();let c:usize=kani::any();let d:usize=kani::any();kani::assume(a<=64&&b<=64&&c<=64&&d<=64);let r=[a..b,c..d];assert_eq!(dep::sum(h,l,&r),reference::sum(h,l,&r)); }
fn pre<const N:usize>(start:usize) {let mut a=qs();let mut b=a;let v=qs::<N>();dep::pre(&mut a,start,&v);reference::pre(&mut b,start,&v);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_preweighted() {let case:u8=kani::any();kani::assume(case<8);match case {0=>pre::<16>(0),1=>pre::<16>(16),2=>pre::<17>(32),3=>pre::<33>(49),4=>pre::<2>(82),5=>pre::<12>(0),6=>pre::<8>(84),_=>pre::<2>(92)}}
#[cfg(feature="optimized-terminal")]
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_preweighted_shared_selector() {let mut a=qs();let mut b=a;let v=qs::<33>();let q=q();dep::shared(&mut a,49,&v,q);reference::shared(&mut b,49,&v,q);assert_eq!(a,b);}
