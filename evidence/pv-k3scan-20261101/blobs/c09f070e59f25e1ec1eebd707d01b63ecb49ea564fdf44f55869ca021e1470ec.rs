use aspis_core::field::{QM31,CM31,M31};
use crate::{host_copy_terminal::access16 as dcopy,reference_copy_terminal::access16 as rcopy,
 host_terminal::access16 as dep,reference_terminal::access16 as reference};
pub(crate) fn q()->QM31 { let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}} }
pub(crate) fn qs<const N:usize>()->[QM31;N] { let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a }
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
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
fn equality_value() {let a=qs();let b=qs();assert_eq!(dep::equality(&a,&b),reference::equality(&a,&b));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high() { let h=qs();let l=qs();let a:usize=kani::any();let b:usize=kani::any();let c:usize=kani::any();let d:usize=kani::any();kani::assume(a<=64&&b<=64&&c<=64&&d<=64);let r=[a..b,c..d];assert_eq!(dep::sum(h,l,&r),reference::sum(h,l,&r)); }
fn pre<const N:usize>(start:usize) {let mut a=qs();let mut b=a;let v=qs::<N>();dep::pre(&mut a,start,&v);reference::pre(&mut b,start,&v);let k:usize=kani::any();kani::assume(k<24);assert_eq!(a[k],b[k]);}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_preweighted() {let case:u8=kani::any();kani::assume(case<8);match case {0=>pre::<16>(0),1=>pre::<16>(16),2=>pre::<17>(32),3=>pre::<33>(49),4=>pre::<2>(82),5=>pre::<12>(0),6=>pre::<8>(84),_=>pre::<2>(92)}}
#[cfg(feature="optimized-terminal")]
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_preweighted_shared_selector() {let mut a=qs();let mut b=a;let v=qs::<33>();let q=q();dep::shared(&mut a,49,&v,q);reference::shared(&mut b,49,&v,q);assert_eq!(a,b);}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement() { let v=qs();let m:u16=kani::any();kani::assume(frozen(m));assert_eq!(crate::statement_copy16::access16::mask(&v,m),rcopy::mask(&v,m)); }
#[cfg(not(feature="optimized-terminal"))]
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn add_digest_binding() { let mut a=qs();let mut b=a;let v=qs();let q=q();let start:usize=kani::any();kani::assume(start<=8);let t:bool=kani::any();let x:[u32;8]=kani::any();let mut d=[M31(0);8];let mut i=0;while i<8 {d[i]=M31(x[i]);i+=1;}dep::digest(&mut a,q,&v,start,&d,t);reference::digest(&mut b,q,&v,start,&d,t);assert_eq!(a,b); }
// Matched mutation control: arbitrary inputs must distinguish a wrong result.
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_wrong() {let v=qs();let m:u16=kani::any();kani::assume(frozen(m));let real=dcopy::mask(&v,m);let mut wrong=rcopy::mask(&v,m);wrong.c0.a.0^=1;assert_eq!(real,wrong);}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_1749() {let v=qs();assert_eq!(dcopy::mask(&v,1749),rcopy::mask(&v,1749));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_2048() {let v=qs();assert_eq!(dcopy::mask(&v,2048),rcopy::mask(&v,2048));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_2049() {let v=qs();assert_eq!(dcopy::mask(&v,2049),rcopy::mask(&v,2049));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_4097() {let v=qs();assert_eq!(dcopy::mask(&v,4097),rcopy::mask(&v,4097));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_6144() {let v=qs();assert_eq!(dcopy::mask(&v,6144),rcopy::mask(&v,6144));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_6145() {let v=qs();assert_eq!(dcopy::mask(&v,6145),rcopy::mask(&v,6145));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_host_26214() {let v=qs();assert_eq!(dcopy::mask(&v,26214),rcopy::mask(&v,26214));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_1749() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,1749),rcopy::mask(&v,1749));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_2048() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,2048),rcopy::mask(&v,2048));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_2049() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,2049),rcopy::mask(&v,2049));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_4097() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,4097),rcopy::mask(&v,4097));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_6144() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,6144),rcopy::mask(&v,6144));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_6145() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,6145),rcopy::mask(&v,6145));}

#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn selector_mask_statement_26214() {let v=qs();assert_eq!(crate::statement_copy16::access16::mask(&v,26214),rcopy::mask(&v,26214));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn external_linear_lazy() {let s=qs::<16>();assert_eq!(crate::deployed_poseidon16::access16::external(s),crate::reference_poseidon16::access16::external(s));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn internal_linear_lazy() {let s=qs::<16>();assert_eq!(crate::deployed_poseidon16::access16::internal(s),crate::reference_poseidon16::access16::internal(s));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn external_linear_packed() {let s=qs::<16>();assert_eq!(crate::deployed_poseidon16::access16::packed(s),crate::reference_poseidon16::access16::packed(s));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn external_local_packed_raw() {let s=qs::<4>();assert_eq!(crate::deployed_poseidon16::access16::raw(s),crate::reference_poseidon16::access16::raw(s));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn full_round() {let s=qs();let c=qs();assert_eq!(crate::deployed_poseidon16::access16::round(s,c),crate::reference_poseidon16::access16::round(s,c));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn full_round_packed() {let s=qs();let c=qs();assert_eq!(crate::deployed_poseidon16::access16::round_packed(s,c),crate::reference_poseidon16::access16::round_packed(s,c));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn full_round_m31_constants() {let s=qs();let c=kani::any();assert_eq!(crate::deployed_poseidon16::access16::round_m31(s,c),crate::reference_poseidon16::access16::round_m31(s,c));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
#[kani::stub(QM31::square,crate::shared_callee16::square)]
fn full_round_m31_constants_packed() {let s=qs();let c=kani::any();assert_eq!(crate::deployed_poseidon16::access16::round_m31_packed(s,c),crate::reference_poseidon16::access16::round_m31_packed(s,c));}

#[kani::proof] #[kani::unwind(128)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
fn shared_repeat16() {let a=q();let b=q();assert_eq!(a.mul(b),a.mul(b));}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(QM31::mul,crate::shared_callee16::mul)]
fn shared_wrong16() {let a=q();let b=q();assert_eq!(a.mul(b),QM31::ZERO);}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn preweighted_scalar92() {pre::<2>(92);}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn sum_high_actual_calls() {let h=qs();let l=qs();assert_eq!(dep::sum(h,l,&[0..57]),reference::sum(h,l,&[0..57]));assert_eq!(dep::sum(h,l,&[4..25,33..57]),reference::sum(h,l,&[4..25,33..57]));assert_eq!(dep::sum(h,l,&[57..63]),reference::sum(h,l,&[57..63]));}
