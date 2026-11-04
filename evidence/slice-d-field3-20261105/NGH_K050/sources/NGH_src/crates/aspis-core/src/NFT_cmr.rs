use super::*;
use crate::field::{CM31,M31,P};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)] struct Call{kind:u8,a:u32,b:u32,reply:u32}
struct Log{calls:[Call;4],count:usize}
fn op(log:&mut Log,kind:u8,a:M31,b:M31)->M31{assert!(a.0<P&&b.0<P&&log.count<4);let reply:u32=kani::any();kani::assume(reply<P);log.calls[log.count]=Call{kind,a:a.0,b:if cfg!(NFT_bad_argument){b.0.wrapping_add(1)}else{b.0},reply};log.count+=1;M31(reply)}
fn logged(value:CM31,log:&mut Log)->CM31{let aa=op(log,0,value.a,M31(0));let real=op(log,1,aa,value.b);let bb=op(log,2,value.b,M31(0));let imag=op(log,3,value.a,bb);CM31::new(real,imag)}
#[kani::proof] #[kani::unwind(15)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn linear_log(){let value=CM31{a:M31(kani::any()),b:M31(kani::any())};kani::assume(value.a.0<P&&value.b.0<P);let mut log=Log{calls:[Call{kind:99,a:0,b:0,reply:0};4],count:0};let got=logged(value,&mut log);assert!(log.count==4);assert!(log.calls[0].kind==0&&log.calls[0].a==value.a.0&&log.calls[0].b==0);assert!(log.calls[1].kind==1&&log.calls[1].a==log.calls[0].reply&&log.calls[1].b==value.b.0);assert!(log.calls[2].kind==2&&log.calls[2].a==value.b.0&&log.calls[2].b==0);assert!(log.calls[3].kind==3&&log.calls[3].a==value.a.0&&log.calls[3].b==log.calls[2].reply);assert!((got.a.0==log.calls[1].reply&&got.b.0==log.calls[3].reply)!=cfg!(NFT_invert));}
#[kani::proof] #[kani::unwind(15)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn log_copy_positive(){let src:Call=Call{kind:kani::any(),a:kani::any(),b:kani::any(),reply:kani::any()};let mut dst:Call=Call{kind:0,a:0,b:0,reply:0};unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src.kind==dst.kind&&src.a==dst.a&&src.b==dst.b&&src.reply==dst.reply);}
#[kani::proof] #[kani::unwind(15)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn log_copy_negative(){let src:Call=Call{kind:kani::any(),a:kani::any(),b:kani::any(),reply:kani::any()};let mut dst:Call=Call{kind:0,a:0,b:0,reply:0};unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src.reply!=dst.reply);}
