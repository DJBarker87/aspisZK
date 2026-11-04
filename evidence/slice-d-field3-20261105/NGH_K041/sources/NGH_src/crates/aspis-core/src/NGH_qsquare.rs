use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
pub(super) fn canonical(x:QM31)->bool{canonical_cm(x.c0)&&canonical_cm(x.c1)}
fn canonical_cm(x:CM31)->bool{x.a.0<P&&x.b.0<P}
fn spec_mul(x:CM31,y:CM31)->CM31{
 let p=P as u64;let a=x.a.0 as u64;let b=x.b.0 as u64;let c=y.a.0 as u64;let d=y.b.0 as u64;
 CM31{a:M31((((a*c)%p+p-(b*d)%p)%p) as u32),b:M31((((a*d)%p+(b*c)%p)%p) as u32)}
}
// No multiplication theorem is checked by Kani. The returned value is
// nondeterministic, constrained by the paired Lean natural-coordinate law.
fn product(x:CM31,y:CM31)->CM31{assert!(canonical_cm(x)&&canonical_cm(y));let z=any_cm();kani::assume(z==spec_mul(x,y));z}
fn square(x:CM31)->CM31{assert!(canonical_cm(x));let z=any_cm();kani::assume(z==spec_mul(x,x));z}
pub(super) fn reference(x:QM31)->QM31{
 let a=x.c0.square();let b=x.c1.square();
 QM31{c0:a.add(mul_by_r(b)),c1:x.c0.mul(x.c1).double()}
}
#[kani::proof_for_contract(QM31::square)]
#[kani::unwind(80)]
#[kani::stub(CM31::square,square)]
#[kani::stub(CM31::mul,product)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn actual_contract(){let x=any_q();kani::assume(canonical(x));x.square();}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let src=any_q();let mut dst=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src==dst);}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src=any_q();let mut dst=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src!=dst);}

#[derive(Clone,Copy)] struct Call{kind:u8,a:CM31,b:CM31,reply:CM31}
struct Log{calls:[Call;3],count:usize}
fn op(log:&mut Log,kind:u8,a:CM31,b:CM31)->CM31{
 assert!(canonical_cm(a)&&canonical_cm(b)&&log.count<3);
 let reply=any_cm();kani::assume(canonical_cm(reply));
 let mut observed=a;if cfg!(NGH_bad_argument)&&log.count==0{observed.a.0^=1;}
 log.calls[log.count]=Call{kind,a:observed,b,reply};log.count+=1;reply
}
// Exact frozen expression with the three field products externalized to LOCAL log.
fn logged(value:QM31,log:&mut Log)->QM31{
 let c0_square=op(log,0,value.c0,CM31::ZERO);
 let c1_square=op(log,1,value.c1,CM31::ZERO);
 QM31{c0:c0_square.add(mul_by_r(c1_square)),c1:op(log,2,value.c0,value.c1).double()}
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn square_log(){
 let value=any_q();kani::assume(canonical(value));
 let mut log=Log{calls:[Call{kind:99,a:CM31::ZERO,b:CM31::ZERO,reply:CM31::ZERO};3],count:0};
 let got=logged(value,&mut log);
 assert!(log.count==3);
 assert!(log.calls[0].kind==0&&log.calls[0].a==value.c0&&log.calls[0].b==CM31::ZERO);
 assert!(log.calls[1].kind==1&&log.calls[1].a==value.c1&&log.calls[1].b==CM31::ZERO);
 assert!(log.calls[2].kind==2&&log.calls[2].a==value.c0&&log.calls[2].b==value.c1);
 let want=QM31{c0:log.calls[0].reply.add(mul_by_r(log.calls[1].reply)),c1:log.calls[2].reply.double()};
 assert!((got==want)!=cfg!(NGH_invert));assert!(canonical(got));
}
