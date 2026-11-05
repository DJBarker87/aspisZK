use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference { include!("NGM_reference.rs"); }
fn qwords(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn fromq(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn rawrow(a:&[K;4])->[[u32;4];4]{[qwords(a[0]),qwords(a[1]),qwords(a[2]),qwords(a[3])]}
pub(super) fn guard_raw_post(r:bool,w:&Weights,folds:usize)->bool{
 let variant=match w.variant{Variant::S1=>0,Variant::S2=>1,Variant::D=>2};
 let reference=reference::guard_raw_ref(variant,folds,rawrow(&w.factors[0][2]),rawrow(&w.factors[2][2]),rawrow(&w.factors[0][3]),rawrow(&w.factors[2][3]));
 let same=r==reference;if cfg!(NGM_invert){!same}else{same}
}
#[kani::proof_for_contract(shared_two_point_guard)] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_raw_contract(){let w=Weights{variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},
 factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|fromq(kani::any())))),
 points:core::array::from_fn(|_|core::array::from_fn(|_|fromq(kani::any()))),extra:core::array::from_fn(|_|fromq(kani::any()))};
 shared_two_point_guard(&w,kani::any());}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_control(){let src:[u8;64]=kani::any();let mut dst:[u8;64]=kani::any();dst.copy_from_slice(&src);let i:usize=kani::any();kani::assume(i<64);assert!((dst[i]==src[i]) != cfg!(NGM_invert));}

mod double_reference{include!("NGM_double_reference.rs");}
struct ProductLog{replies:[K;2],left:[K;2],right:[K;2],count:usize}
fn opaque_product(x:K,y:K,log:&mut ProductLog)->K{let i=log.count;log.left[i]=x;log.right[i]=y;log.count+=1;log.replies[i]}
fn source_double(x:K,log:&mut ProductLog)->K{opaque_product(x,x,log).add(opaque_product(x,x,log)).sub(K::ONE)}
fn canonical_q()->K{let x:[u32;4]=kani::any();for word in x{kani::assume(word<0x7fffffff);}fromq(x)}
fn exercise_double(group:u8){let x=canonical_q();let mut log=ProductLog{replies:[canonical_q(),canonical_q()],left:[K::ZERO;2],right:[K::ZERO;2],count:0};let expected=double_reference::double_observed_ref(qwords(log.replies[0]),qwords(log.replies[1]));let out=qwords(source_double(x,&mut log));let good=match group{0=>out[0]==expected[0],1=>out[1]==expected[1],2=>out[2]==expected[2],3=>out[3]==expected[3],4=>log.count==2,5=>log.left[0]==x&&log.right[0]==x,6=>log.left[1]==x&&log.right[1]==x,_=>false};assert!(good != cfg!(NGM_invert));}
macro_rules! double_gate{($n:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(17)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]fn $n(){exercise_double($g)}};}
double_gate!(double_control_0,0);
double_gate!(double_control_1,1);
double_gate!(double_control_2,2);
double_gate!(double_control_3,3);
double_gate!(double_control_4,4);
double_gate!(double_control_5,5);
double_gate!(double_control_6,6);
