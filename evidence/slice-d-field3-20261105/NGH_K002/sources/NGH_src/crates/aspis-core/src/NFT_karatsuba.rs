use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{a:CM31,reply:CM31,count:u8}
fn mul_r(log:&mut Log,value:CM31)->CM31{assert!(value.a.0<P&&value.b.0<P);log.a=value;log.count+=1;let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P);let reply=CM31{a:M31(a),b:M31(b)};log.reply=reply;reply}
fn reconstructed(c:[u64;3])->CM31{let a=M31::reduce_u64(c[0]);let b=M31::reduce_u64(c[1]);let t=M31::reduce_u64(c[2]);CM31{a:a.sub(b),b:t.sub(a).sub(b)}}
fn from_logged(sums:[[u64;3];3],log:&mut Log)->QM31{
    let reconstruct = |channels: [u64; 3]| {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 {
            a: m0.sub(m1),
            b: m2.sub(m0).sub(m1),
        }
    };
    let m0 = reconstruct(sums[0]);
    let m1 = reconstruct(sums[1]);
    let m2 = reconstruct(sums[2]);
    QM31 {
        c0: m0.add(mul_r(log,m1)),
        c1: m2.sub(m0).sub(m1),
    }
}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn reconstruct_log(){let sums:[[u64;3];3]=kani::any();let mut log=Log{a:CM31::ZERO,reply:CM31::ZERO,count:0};let got=from_logged(sums,&mut log);let m0=reconstructed(sums[0]);let m1=reconstructed(sums[1]);let m2=reconstructed(sums[2]);assert!(log.count==1&&log.a==m1);let want=QM31{c0:m0.add(log.reply),c1:m2.sub(m0).sub(m1)};assert!((got==want)!=cfg!(NFT_invert));assert!(got.c0.a.0<P&&got.c0.b.0<P&&got.c1.a.0<P&&got.c1.b.0<P);}
