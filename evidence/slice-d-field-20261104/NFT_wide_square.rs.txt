use super::*;
use crate::field::{CM31,M31,P};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
#[derive(Clone,Copy)] struct Call{kind:u8,a:QM31,b:QM31,reply:QM31}
struct Log{calls:[Call;4],count:usize}
fn op(log:&mut Log,kind:u8,a:QM31,b:QM31)->QM31{assert!(canonical(a)&&canonical(b)&&log.count<4);let r=any_q();kani::assume(canonical(r));let mut observed=a;if cfg!(NFT_bad_argument)&&log.count==0{observed.c0.a.0^=1;}log.calls[log.count]=Call{kind,a:observed,b,reply:r};log.count+=1;r}
// Frozen wide square with the four product/square/mul_u sites externalized;
// let bindings preserve Rust's source evaluation order.
fn logged(value:WideExact,log:&mut Log)->WideExact{let cross=op(log,0,value.c0,value.c1);let aa=op(log,1,value.c0,QM31::ZERO);let bb=op(log,2,value.c1,QM31::ZERO);let u=op(log,3,bb,QM31::ZERO);WideExact{c0:aa.add(u),c1:cross.add(cross)}}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn square_log(){let value=WideExact{c0:any_q(),c1:any_q()};kani::assume(canonical(value.c0)&&canonical(value.c1));let mut log=Log{calls:[Call{kind:99,a:QM31::ZERO,b:QM31::ZERO,reply:QM31::ZERO};4],count:0};let got=logged(value,&mut log);assert!(log.count==4);assert!(log.calls[0].kind==0&&log.calls[0].a==value.c0&&log.calls[0].b==value.c1);assert!(log.calls[1].kind==1&&log.calls[1].a==value.c0&&log.calls[1].b==QM31::ZERO);assert!(log.calls[2].kind==2&&log.calls[2].a==value.c1&&log.calls[2].b==QM31::ZERO);assert!(log.calls[3].kind==3&&log.calls[3].a==log.calls[2].reply&&log.calls[3].b==QM31::ZERO);let want=WideExact{c0:log.calls[1].reply.add(log.calls[3].reply),c1:log.calls[0].reply.add(log.calls[0].reply)};assert!((got==want)!=cfg!(NFT_invert));assert!(canonical(got.c0)&&canonical(got.c1));}
