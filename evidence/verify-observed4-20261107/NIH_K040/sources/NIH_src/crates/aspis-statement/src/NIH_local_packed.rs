use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct NIH_Log { input:[[u32;4];4], reply:[u64;4], calls:usize }
fn NIH_raw(input:[QM31;4],log:&mut NIH_Log)->[u64;4]{
 assert_eq!(log.calls,0);log.input=input.map(extension_limbs);log.calls+=1;log.reply
}
fn NIH_local(input: [QM31; 4], log: &mut NIH_Log) -> QM31 {
    extension_from_raw_limbs(NIH_raw(input,log))
}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_local_packed(){
 let w:[[u32;4];4]=kani::any();
 kani::assume(w[0][0]<2147483647&&w[0][1]<2147483647&&w[0][2]<2147483647&&w[0][3]<2147483647&&w[1][0]<2147483647&&w[1][1]<2147483647&&w[1][2]<2147483647&&w[1][3]<2147483647&&w[2][0]<2147483647&&w[2][1]<2147483647&&w[2][2]<2147483647&&w[2][3]<2147483647&&w[3][0]<2147483647&&w[3][1]<2147483647&&w[3][2]<2147483647&&w[3][3]<2147483647);
 let input=w.map(|a|QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}});
 let reply:[u64;4]=kani::any();kani::assume(reply[0]<4611686018427387904&&reply[1]<4611686018427387904&&reply[2]<4611686018427387904&&reply[3]<4611686018427387904);
 let mut log=NIH_Log{input:kani::any(),reply,calls:0};let out=extension_limbs(NIH_local(input,&mut log));
 let j:usize=kani::any();let r:usize=kani::any();kani::assume(j<4&&r<4);
 assert_eq!(log.calls,1);assert_eq!(log.input[r][j],w[r][j]);assert_eq!(log.reply[j],reply[j]);
 assert_eq!(out[j],(reply[j]%2147483647) as u32 ^ if cfg!(NIH_invert){1}else{0});
}
