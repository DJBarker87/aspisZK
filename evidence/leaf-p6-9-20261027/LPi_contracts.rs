//! Lean-discharged byte stubs. Pairing: LPi_WriterValues.
use aspis_core::field::{CM31,QM31,M31};
fn word(x:M31)->[u8;4] { [x.0 as u8,(x.0>>8) as u8,(x.0>>16) as u8,(x.0>>24) as u8] }
pub fn mbytes(x:M31)->[u8;4] {
 let b:[u8;4]=kani::any();kani::assume(b==word(x));b
}
pub fn cbytes(x:CM31,out:&mut[u8]) {
 assert!(out.len()==8);
 let a=word(x.a);let b=word(x.b);let v:[u8;8]=kani::any();
 kani::assume(v==[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]]);
 out.copy_from_slice(&v);
}
pub fn qbytes(x:QM31,out:&mut[u8]) {
 assert!(out.len()==16);
 let a=word(x.c0.a);let b=word(x.c0.b);let c=word(x.c1.a);let d=word(x.c1.b);
 let v:[u8;16]=kani::any();
 kani::assume(v==[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3]]);
 out.copy_from_slice(&v);
}
fn q(x:[u32;4])->QM31 {QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn check_q<const N:usize,const AT:usize>() {
 let x:[u32;4]=kani::any();let mut buf:[u8;N]=kani::any();let before=buf;
 q(x).write_le_bytes(&mut buf[AT..AT+16]);
 let j:usize=kani::any();kani::assume(j<N);
 if j>=AT&&j<AT+16 {let k=j-AT;assert_eq!(buf[j],(x[k/4]>>((k%4)*8)) as u8);}
 else {assert_eq!(buf[j],before[j]);}
 kani::cover!(j==AT+15);kani::cover!(x[0]==u32::MAX);
}
macro_rules! qcase {($name:ident,$n:expr,$at:expr)=>{
 #[kani::proof] #[kani::stub(CM31::write_le_bytes,cbytes)] #[kani::unwind(18)]
 fn $name(){check_q::<$n,$at>();}
}}
qcase!(q_owned16,16,0);
qcase!(q_parent32_left,32,0);
qcase!(q_parent32_right,32,16);
qcase!(q_parent32_middle,32,8);
qcase!(q_parent48_middle,48,16);
qcase!(q_parent48_right,48,32);
fn check_c<const N:usize,const AT:usize>() {
 let x:[u32;2]=kani::any();let mut buf:[u8;N]=kani::any();let before=buf;
 CM31{a:M31(x[0]),b:M31(x[1])}.write_le_bytes(&mut buf[AT..AT+8]);
 let j:usize=kani::any();kani::assume(j<N);
 if j>=AT&&j<AT+8 {let k=j-AT;assert_eq!(buf[j],(x[k/4]>>((k%4)*8)) as u8);}
 else {assert_eq!(buf[j],before[j]);}
 kani::cover!(j==AT+7);kani::cover!(x[1]==u32::MAX);
}
macro_rules! ccase {($name:ident,$n:expr,$at:expr)=>{
 #[kani::proof] #[kani::stub(M31::to_le_bytes,mbytes)] #[kani::unwind(10)]
 fn $name(){check_c::<$n,$at>();}
}}
ccase!(c_parent16_left,16,0);
ccase!(c_parent16_right,16,8);
ccase!(c_parent32_middle,32,16);
