use super::*;
#[path="NEB_additive_reference.rs"] pub mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
impl kani::Arbitrary for M31 {fn any()->Self{M31(kani::any::<u32>())}}
pub fn canon_m(x:M31)->bool{x.0<P}
pub fn canon_c(x:CM31)->bool{canon_m(x.a)&&canon_m(x.b)}
pub fn canon_q(x:QM31)->bool{canon_c(x.c0)&&canon_c(x.c1)}
pub fn any_m()->M31{M31(kani::any())}
pub fn any_c()->CM31{CM31{a:any_m(),b:any_m()}}
pub fn any_q()->QM31{QM31{c0:any_c(),c1:any_c()}}
pub fn words_c(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
pub fn words_q(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
pub fn post_m_add(x:M31,y:M31,r:M31)->bool {let good=r.0==reference::add_word(x.0,y.0) && canon_m(r);if cfg!(NEB_wrong_m_add){!good}else{good}}
#[kani::proof_for_contract(M31::add)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn m_add(){let x=any_m();kani::assume(canon_m(x));let y=any_m();kani::assume(canon_m(y));let _=x.add(y);}
pub fn post_m_sub(x:M31,y:M31,r:M31)->bool {let good=r.0==reference::sub_word(x.0,y.0) && canon_m(r);if cfg!(NEB_wrong_m_sub){!good}else{good}}
#[kani::proof_for_contract(M31::sub)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn m_sub(){let x=any_m();kani::assume(canon_m(x));let y=any_m();kani::assume(canon_m(y));let _=x.sub(y);}
pub fn post_m_double(x:M31,r:M31)->bool {let good=r.0==reference::add_word(x.0,x.0) && canon_m(r);if cfg!(NEB_wrong_m_double){!good}else{good}}
#[kani::proof_for_contract(M31::double)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::add)]
fn m_double(){let x=any_m();kani::assume(canon_m(x));let _=x.double();}
pub fn post_c_add(x:CM31,y:CM31,r:CM31)->bool {let want=reference::add2(words_c(x),words_c(y));let good=r.a.0==want[0] && r.b.0==want[1] && canon_c(r);if cfg!(NEB_wrong_c_add){!good}else{good}}
#[kani::proof_for_contract(CM31::add)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::add)]
fn c_add(){let x=any_c();kani::assume(canon_c(x));let y=any_c();kani::assume(canon_c(y));let _=x.add(y);}
pub fn post_c_sub(x:CM31,y:CM31,r:CM31)->bool {let want=reference::sub2(words_c(x),words_c(y));let good=r.a.0==want[0] && r.b.0==want[1] && canon_c(r);if cfg!(NEB_wrong_c_sub){!good}else{good}}
#[kani::proof_for_contract(CM31::sub)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::sub)]
fn c_sub(){let x=any_c();kani::assume(canon_c(x));let y=any_c();kani::assume(canon_c(y));let _=x.sub(y);}
pub fn post_c_double(x:CM31,r:CM31)->bool {let want=reference::add2(words_c(x),words_c(x));let good=r.a.0==want[0] && r.b.0==want[1] && canon_c(r);if cfg!(NEB_wrong_c_double){!good}else{good}}
#[kani::proof_for_contract(CM31::double)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::add)]
fn c_double(){let x=any_c();kani::assume(canon_c(x));let _=x.double();}
pub fn post_q_add(x:QM31,y:QM31,r:QM31)->bool {let want=reference::add4(words_q(x),words_q(y));let good=r.c0.a.0==want[0] && r.c0.b.0==want[1] && r.c1.a.0==want[2] && r.c1.b.0==want[3] && canon_q(r);if cfg!(NEB_wrong_q_add){!good}else{good}}
#[kani::proof_for_contract(QM31::add)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::add)]
fn q_add(){let x=any_q();kani::assume(canon_q(x));let y=any_q();kani::assume(canon_q(y));let _=x.add(y);}
pub fn post_q_sub(x:QM31,y:QM31,r:QM31)->bool {let want=reference::sub4(words_q(x),words_q(y));let good=r.c0.a.0==want[0] && r.c0.b.0==want[1] && r.c1.a.0==want[2] && r.c1.b.0==want[3] && canon_q(r);if cfg!(NEB_wrong_q_sub){!good}else{good}}
#[kani::proof_for_contract(QM31::sub)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(M31::sub)]
fn q_sub(){let x=any_q();kani::assume(canon_q(x));let y=any_q();kani::assume(canon_q(y));let _=x.sub(y);}
#[kani::ensures(|r| r[0]==x)]
fn weak_array(x:u32)->[u32;8]{[x;8]}
#[kani::proof_for_contract(weak_array)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_weak(){let _=weak_array(kani::any());}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real(){let x:u32=kani::any();assert_eq!(weak_array(x)[7],x);}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(weak_array)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_unimplied(){let x:u32=kani::any();assert_eq!(weak_array(x)[7],x);}
#[kani::modifies(x)] #[kani::ensures(|r| r[0]==0)]
fn bad_array_frame(x:&mut u32,y:&mut u32)->[u32;8]{let _=x;*y=y.wrapping_add(1);[0;8]}
#[kani::proof_for_contract(bad_array_frame)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_frame(){let mut x:u32=kani::any();let mut y:u32=kani::any();let _=bad_array_frame(&mut x,&mut y);}
