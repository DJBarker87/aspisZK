use super::*;
fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
fn words(x:WideExact)->[u32;8]{[x.c0.c0.a.0,x.c0.c0.b.0,x.c0.c1.a.0,x.c0.c1.b.0,x.c1.c0.a.0,x.c1.c0.b.0,x.c1.c1.a.0,x.c1.c1.b.0]}
fn canon(w:[u32;8])->bool{w[0]<P&&w[1]<P&&w[2]<P&&w[3]<P&&w[4]<P&&w[5]<P&&w[6]<P&&w[7]<P}
#[kani::proof]
fn NBG_limbs(){
 let w:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8);
 match WideExact::from_limbs(w){None=>assert!(!canon(w)),Some(x)=>{assert!(canon(w));assert!(words(x)[i]==w[i]);assert!(x.to_limbs()[i]==w[i]);}}
 kani::cover!(w[7]==P);
}
#[kani::proof]
fn NBG_wide_constructors(){
 let w:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8);
 let a=q([w[0],w[1],w[2],w[3]]);let b=q([w[4],w[5],w[6],w[7]]);
 let x=WideExact::new(a,b);assert!(words(x)[i]==w[i]%P);
 let y=WideExact::from_qm31(a);assert!(words(y)[i]==if i<4{w[i]%P}else{0});
 let c=super::canonical_qm31(a);let z=WideExact{c0:c,c1:b};
 assert!(z.c0().c0.a.0==c.c0.a.0&&z.c0().c0.b.0==c.c0.b.0&&z.c0().c1.a.0==c.c1.a.0&&z.c0().c1.b.0==c.c1.b.0);
 assert!(z.c1().c0.a.0==b.c0.a.0&&z.c1().c0.b.0==b.c0.b.0&&z.c1().c1.a.0==b.c1.a.0&&z.c1().c1.b.0==b.c1.b.0);
 kani::cover!(w[0]==u32::MAX);
}
#[kani::proof]
fn NBG_wide_add_sub(){
 let a:[u32;8]=kani::any();let b:[u32;8]=kani::any();kani::assume(canon(a)&&canon(b));
 let x=WideExact{c0:q([a[0],a[1],a[2],a[3]]),c1:q([a[4],a[5],a[6],a[7]])};let y=WideExact{c0:q([b[0],b[1],b[2],b[3]]),c1:q([b[4],b[5],b[6],b[7]])};
 let i:usize=kani::any();kani::assume(i<8);let sum=a[i]as u64+b[i]as u64;let diff=a[i]as u64+P as u64-b[i]as u64;
 assert!(words(x.add(y))[i]==(if sum>=P as u64{sum-P as u64}else{sum})as u32);
 assert!(words(x.sub(y))[i]==(if diff>=P as u64{diff-P as u64}else{diff})as u32);
 kani::cover!(i==7&&a[7]==P-1);
}
#[kani::proof]
fn NBG_wide_decode(){
 let b:[u8;33]=kani::any();let n:usize=kani::any();kani::assume(n<=33);
 let out=WideExact::from_le_bytes(&b[..n]);
 if n!=32 {assert!(out.is_none());} else {
 let w=[u32::from_le_bytes([b[0],b[1],b[2],b[3]]),u32::from_le_bytes([b[4],b[5],b[6],b[7]]),u32::from_le_bytes([b[8],b[9],b[10],b[11]]),u32::from_le_bytes([b[12],b[13],b[14],b[15]]),u32::from_le_bytes([b[16],b[17],b[18],b[19]]),u32::from_le_bytes([b[20],b[21],b[22],b[23]]),u32::from_le_bytes([b[24],b[25],b[26],b[27]]),u32::from_le_bytes([b[28],b[29],b[30],b[31]])];
 match out{None=>assert!(!canon(w)),Some(x)=>{assert!(canon(w));let i:usize=kani::any();kani::assume(i<8);assert!(words(x)[i]==w[i]);}}
 }
 kani::cover!(n==33);
}
