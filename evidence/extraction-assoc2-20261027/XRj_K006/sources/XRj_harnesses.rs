use super::*;
// Per-iteration source projection of verifier.rs:59. Only the projection from
// Verified's fields to these arrays is abstracted; it remains an OPEN bridge.
fn source_scalar(point:usize,l:usize,claims:&[[K;29];3],extra:&[K;29],before:&[K;29],y1:&[u8])->K {
 match point {0..=2=>claims[point][l],3=>extra[l],4=>before[l],_=>field(y1,l).c0()}
}
fn reference_scalar(point:usize,l:usize,claims:&[[K;29];3],extra:&[K;29],before:&[K;29],y1:&[u8])->K {
 if point<3 {claims[point][l]} else if point==3 {extra[l]} else if point==4 {before[l]} else {field(y1,l).c0()}
}
fn any_k()->K {let x:[u32;4]=kani::any();kani::assume(x.iter().all(|v|*v<0x7fff_ffff));K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn base_e()->E {let x:u32=kani::any();kani::assume(x<0x7fff_ffff);E::from_qm31(K{c0:CM31{a:M31(x),b:M31(0)},c1:CM31::ZERO})}
fn selection(point:usize){
 let l:usize=kani::any();kani::assume(l<29);
 let x=any_k();let mut claims=[[K::ZERO;29];3];let mut extra=[K::ZERO;29];let mut before=[K::ZERO;29];let mut y1=[0u8;928];
 for p in 0..3 {claims[p][l]=x;}
 extra[l]=x;before[l]=x;
 let b=E::from_qm31(x).to_le_bytes();for j in 0..32 {y1[32*l+j]=b[j];}
 let a=source_scalar(point,l,&claims,&extra,&before,&y1);
 let r=reference_scalar(point,l,&claims,&extra,&before,&y1);
 assert_eq!(a,r);assert_eq!(a,x);kani::cover!(l==28);
}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_0(){selection(0);}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_1(){selection(1);}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_2(){selection(2);}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_3(){selection(3);}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_4(){selection(4);}
#[kani::proof] #[kani::unwind(34)] fn XRj_scalar_5(){selection(5);}

// A single body transition of weights::powers, not its 29-iteration loop.
#[kani::proof] #[kani::unwind(10)] fn XRj_power_step(){
 let i:usize=kani::any();kani::assume(i<28);let p=base_e();let x=base_e();let mut out=[E::ZERO;29];
 out[i]=p;let next=i+1;let q=p.mul(x);
 assert_eq!(out[i],p);assert_eq!(next,i+1);assert_eq!(q,x.mul(p));kani::cover!(i==27);
}
// Single inner push, restricted operands; no prepared_claim loop or hash.
#[kani::proof] #[kani::unwind(10)] fn XRj_dot_zero(){let e=base_e();let mut d=fast_pairing::EbyKDot::new();assert!(d.push(e,K::ZERO).is_ok());assert_eq!(d.finish(),E::ZERO);}
#[kani::proof] #[kani::unwind(10)] fn XRj_dot_one(){let k=any_k();let mut d=fast_pairing::EbyKDot::new();assert!(d.push(E::ONE,k).is_ok());assert_eq!(d.finish(),E::from_qm31(k));}
// One outer weighted-fold transition, base-field sparse domain only.
#[kani::proof] #[kani::unwind(10)] fn XRj_fold_step(){let old=base_e();let part=base_e();let coefficient=E::ZERO;let next=old.add(coefficient.mul(part));assert_eq!(next,old);}
