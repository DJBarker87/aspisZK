//! Generic tower inverse control; checked lower arithmetic is parametric.
use aspis_core::{field::{M31,CM31 as C,QM31 as Q,WideExact as E,P},r0::CodeField};
use super::{reference_tower_field as r,reference_scalar::CodeField as RefCodeField};
static mut REPLAY:bool=false;
static mut COUNT:usize=0;
static mut TAGS:[u32;32]=[0;32];
static mut LEFT:[[u32;8];32]=[[0;8];32];
static mut RIGHT:[[u32;8];32]=[[0;8];32];
static mut ANSWERS:[[u32;8];32]=[[0;8];32];
fn op(tag:u32,a:[u32;8],b:[u32;8])->[u32;8] {
 let i=unsafe{COUNT};assert!(i<32);
 if unsafe{REPLAY} {assert_eq!(unsafe{TAGS[i]},tag);assert_eq!(unsafe{LEFT[i]},a);assert_eq!(unsafe{RIGHT[i]},b);}
 else {unsafe{TAGS[i]=tag;LEFT[i]=a;RIGHT[i]=b;}}
 unsafe{COUNT=i+1;ANSWERS[i]}
}
macro_rules! binary {($name:ident,$t:ty,$raw:ident,$new:ident,$tag:expr)=>{pub(crate) fn $name(a:$t,b:$t)->$t {$new(op($tag,$raw(a),$raw(b)))}};}
macro_rules! unary {($name:ident,$t:ty,$raw:ident,$new:ident,$tag:expr)=>{pub(crate) fn $name(a:$t)->$t {$new(op($tag,$raw(a),[0;8]))}};}
fn mraw(x:M31)->[u32;8] {[x.0,0,0,0,0,0,0,0]}
fn craw(x:C)->[u32;8] {[x.a.0,x.b.0,0,0,0,0,0,0]}
fn qraw(x:Q)->[u32;8] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0,0,0,0,0]}
fn mnew(a:[u32;8])->M31 {M31(a[0])}
fn cnew(a:[u32;8])->C {C::new(M31(a[0]),M31(a[1]))}
fn qnew(a:[u32;8])->Q {Q{c0:cnew(a),c1:C::new(M31(a[2]),M31(a[3]))}}
fn rmraw(x:r::M31)->[u32;8] {[x.0,0,0,0,0,0,0,0]}
fn rcraw(x:r::CM31)->[u32;8] {[x.a.0,x.b.0,0,0,0,0,0,0]}
fn rqraw(x:r::QM31)->[u32;8] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0,0,0,0,0]}
fn rmnew(a:[u32;8])->r::M31 {r::M31(a[0])}
fn rcnew(a:[u32;8])->r::CM31 {r::CM31::new(r::M31(a[0]),r::M31(a[1]))}
fn rqnew(a:[u32;8])->r::QM31 {r::QM31{c0:rcnew(a),c1:r::CM31::new(r::M31(a[2]),r::M31(a[3]))}}
binary!(madd,M31,mraw,mnew,1);
binary!(msub,M31,mraw,mnew,2);
unary!(mneg,M31,mraw,mnew,3);
binary!(mmul,M31,mraw,mnew,4);
binary!(cadd,C,craw,cnew,11);
binary!(csub,C,craw,cnew,12);
unary!(cneg,C,craw,cnew,13);
binary!(cmul,C,craw,cnew,14);
binary!(qadd,Q,qraw,qnew,21);
binary!(qsub,Q,qraw,qnew,22);
unary!(qneg,Q,qraw,qnew,23);
binary!(qmul,Q,qraw,qnew,24);
binary!(rmadd,r::M31,rmraw,rmnew,1);
binary!(rmsub,r::M31,rmraw,rmnew,2);
unary!(rmneg,r::M31,rmraw,rmnew,3);
binary!(rmmul,r::M31,rmraw,rmnew,4);
binary!(rcadd,r::CM31,rcraw,rcnew,11);
binary!(rcsub,r::CM31,rcraw,rcnew,12);
unary!(rcneg,r::CM31,rcraw,rcnew,13);
binary!(rcmul,r::CM31,rcraw,rcnew,14);
binary!(rqadd,r::QM31,rqraw,rqnew,21);
binary!(rqsub,r::QM31,rqraw,rqnew,22);
unary!(rqneg,r::QM31,rqraw,rqnew,23);
binary!(rqmul,r::QM31,rqraw,rqnew,24);
pub(crate) fn current_minv(x:M31)->Option<M31> {
 let answer=op(100,mraw(x),[0;8]);if x.0==0 {None} else {Some(M31(answer[0]))}
}
pub(crate) fn old_minv(x:r::M31)->Option<r::M31> {
 let answer=op(100,rmraw(x),[0;8]);if x.0==0 {None} else {Some(r::M31(answer[0]))}
}
fn begin(answers:[[u32;8];32]) {unsafe{REPLAY=false;COUNT=0;ANSWERS=answers;}}
fn replay()->usize {let n=unsafe{COUNT};unsafe{REPLAY=true;COUNT=0;}n}
#[kani::proof]
#[kani::stub(<M31 as CodeField>::try_inv,current_minv)]
#[kani::unwind(40)]
#[kani::stub(aspis_core::field::M31::add,madd)]
#[kani::stub(aspis_core::field::M31::neg,mneg)]
#[kani::stub(aspis_core::field::M31::mul,mmul)]
#[kani::stub(aspis_core::field::CM31::sub,csub)]
#[kani::stub(aspis_core::field::CM31::neg,cneg)]
#[kani::stub(aspis_core::field::CM31::mul,cmul)]
#[kani::stub(aspis_core::field::QM31::sub,qsub)]
#[kani::stub(aspis_core::field::QM31::neg,qneg)]
#[kani::stub(aspis_core::field::QM31::mul,qmul)]
fn generic_tower_inverse_trace() {
 let input:[u32;8]=kani::any();for x in input {kani::assume(x<P);}
 let answers:[[u32;8];32]=kani::any();for a in answers {for x in a {kani::assume(x<P);}}
 begin(answers);
 let expected=<r::CM31 as RefCodeField>::try_inv(rcnew(input)).map(rcraw);
 let count=replay();let actual=<C as CodeField>::try_inv(cnew(input)).map(craw);
 assert_eq!(actual,expected);assert_eq!(unsafe{COUNT},count);
 begin(answers);
 let expected=<r::QM31 as RefCodeField>::try_inv(rqnew(input)).map(rqraw);
 let count=replay();let actual=<Q as CodeField>::try_inv(qnew(input)).map(qraw);
 assert_eq!(actual,expected);assert_eq!(unsafe{COUNT},count);
 begin(answers);
 let expected=<r::WideExact as RefCodeField>::try_inv(r::WideExact::from_limbs(input).unwrap()).map(|x|x.to_limbs());
 let count=replay();let actual=<E as CodeField>::try_inv(E::from_limbs(input).unwrap()).map(|x|x.to_limbs());
 assert_eq!(actual,expected);assert_eq!(unsafe{COUNT},count);
}
