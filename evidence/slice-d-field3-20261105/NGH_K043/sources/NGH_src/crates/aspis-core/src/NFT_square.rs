use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{wide_args:(u64,u64),mul_args:(u32,u32),wide_reply:u64,mul_reply:u32,count:u8}
fn product(log:&mut Log,a:u64,b:u64)->u64{assert!(log.count==0);log.count=1;log.wide_args=(a,b);let r:u64=kani::any();log.wide_reply=r;r}
fn multiply(log:&mut Log,a:M31,b:M31)->M31{assert!(log.count==1);assert!(a.0<P&&b.0<P);log.count=2;log.mul_args=(a.0,b.0);let r:u32=kani::any();kani::assume(r<P);log.mul_reply=r;M31(r)}
// Frozen CM31::square expression with ONLY the two multiplication sites
// replaced by local-record opaque calls. The erasure map is committed.
fn square_logged(value:CM31,log:&mut Log)->CM31{
 CM31{
 a:M31::reduce_u64(product(log,u64::from(value.a.0)+u64::from(value.b.0),u64::from(value.a.0)+u64::from(P)-u64::from(value.b.0))),
 b:multiply(log,value.a,value.b).double(),
 }
}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn square_log(){
 let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P);
 let value=CM31{a:M31(a),b:M31(b)};
 let mut log=Log{wide_args:(0,0),mul_args:(0,0),wide_reply:0,mul_reply:0,count:0};
 let got=square_logged(value,&mut log);
 assert!(log.count==2);
 assert!(log.wide_args==(a as u64+b as u64,a as u64+P as u64-b as u64));
 assert!(log.mul_args==(a,b));
 assert!(got.a.0==M31::reduce_u64(log.wide_reply).0);
 let expected=M31(log.mul_reply).double().0;
 assert!(got.b.0==if cfg!(NFT_invert){expected^1}else{expected});
}

#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_cm_positive(){let src=CM31{a:M31(kani::any()),b:M31(kani::any())};let mut dst=CM31::ZERO;unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.a.0==src.a.0&&dst.b.0==src.b.0);}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_cm_negative(){let src=CM31{a:M31(kani::any()),b:M31(kani::any())};let mut dst=CM31::ZERO;unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.b.0!=src.b.0);}
