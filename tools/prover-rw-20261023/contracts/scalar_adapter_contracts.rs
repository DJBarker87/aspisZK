//! CodeField arithmetic adapters forward exactly once to checked scalar kernels.
use aspis_core::{field::{WideExact as E,QM31 as Q,CM31 as C,M31,P},r0::CodeField};
static mut COUNT:usize=0;
static mut TAG:u32=0;
static mut LEFT:[u32;8]=[0;8];
static mut RIGHT:[u32;8]=[0;8];
static mut ANSWER:[u32;8]=[0;8];
fn operation(tag:u32,a:[u32;8],b:[u32;8])->[u32;8] {
    assert_eq!(unsafe{COUNT},0);assert_eq!(unsafe{TAG},tag);
    assert_eq!(unsafe{LEFT},a);assert_eq!(unsafe{RIGHT},b);
    unsafe{COUNT=1;ANSWER}
}
fn prepare(tag:u32,a:[u32;8],b:[u32;8],answer:[u32;8]) {
    unsafe{COUNT=0;TAG=tag;LEFT=a;RIGHT=b;ANSWER=answer;}
}
fn mraw(x:M31)->[u32;8] {[x.0,0,0,0,0,0,0,0]}
fn qraw(x:Q)->[u32;8] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0,0,0,0,0]}
fn eraw(x:E)->[u32;8] {x.to_limbs()}
fn mnew(a:[u32;8])->M31 {M31(a[0])}
fn qnew(a:[u32;8])->Q {Q{c0:C::new(M31(a[0]),M31(a[1])),c1:C::new(M31(a[2]),M31(a[3]))}}
fn enew(a:[u32;8])->E {E::from_limbs(a).unwrap()}
macro_rules! binary {($name:ident,$t:ty,$raw:ident,$new:ident,$tag:expr)=>{
    fn $name(a:$t,b:$t)->$t {$new(operation($tag,$raw(a),$raw(b)))}
};}
macro_rules! unary {($name:ident,$t:ty,$raw:ident,$new:ident,$tag:expr)=>{
    fn $name(a:$t)->$t {$new(operation($tag,$raw(a),[0;8]))}
};}
binary!(madd,M31,mraw,mnew,1);binary!(msub,M31,mraw,mnew,2);unary!(mneg,M31,mraw,mnew,3);binary!(mmul,M31,mraw,mnew,4);
binary!(qadd,Q,qraw,qnew,1);binary!(qsub,Q,qraw,qnew,2);unary!(qneg,Q,qraw,qnew,3);binary!(qmul,Q,qraw,qnew,4);
binary!(eadd,E,eraw,enew,1);binary!(esub,E,eraw,enew,2);unary!(eneg,E,eraw,enew,3);binary!(emul,E,eraw,enew,4);
macro_rules! verify {($t:ty,$raw:ident,$new:ident,$a:ident,$b:ident,$answer:ident)=>{{
    let a=$new($a);let b=$new($b);let expected=$raw($new($answer));
    prepare(1,$raw(a),$raw(b),$answer);assert_eq!($raw(<$t as CodeField>::add(a,b)),expected);assert_eq!(unsafe{COUNT},1);
    prepare(2,$raw(a),$raw(b),$answer);assert_eq!($raw(<$t as CodeField>::sub(a,b)),expected);assert_eq!(unsafe{COUNT},1);
    prepare(3,$raw(a),[0;8],$answer);assert_eq!($raw(<$t as CodeField>::neg(a)),expected);assert_eq!(unsafe{COUNT},1);
    prepare(4,$raw(a),$raw(b),$answer);assert_eq!($raw(<$t as CodeField>::mul(a,b)),expected);assert_eq!(unsafe{COUNT},1);
}};}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(aspis_core::field::M31::add,madd)]
#[kani::stub(aspis_core::field::M31::sub,msub)]
#[kani::stub(aspis_core::field::M31::neg,mneg)]
#[kani::stub(aspis_core::field::M31::mul,mmul)]
#[kani::stub(aspis_core::field::QM31::add,qadd)]
#[kani::stub(aspis_core::field::QM31::sub,qsub)]
#[kani::stub(aspis_core::field::QM31::neg,qneg)]
#[kani::stub(aspis_core::field::QM31::mul,qmul)]
#[kani::stub(aspis_core::field::WideExact::add,eadd)]
#[kani::stub(aspis_core::field::WideExact::sub,esub)]
#[kani::stub(aspis_core::field::WideExact::neg,eneg)]
#[kani::stub(aspis_core::field::WideExact::mul,emul)]
fn arithmetic_forwarding() {
    let a:[u32;8]=kani::any();let b:[u32;8]=kani::any();let answer:[u32;8]=kani::any();
    for x in a {kani::assume(x<P);}for x in b {kani::assume(x<P);}for x in answer {kani::assume(x<P);}
    verify!(M31,mraw,mnew,a,b,answer);verify!(Q,qraw,qnew,a,b,answer);verify!(E,eraw,enew,a,b,answer);
}
