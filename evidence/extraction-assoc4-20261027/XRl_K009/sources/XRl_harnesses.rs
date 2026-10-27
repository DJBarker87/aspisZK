use super::*;
// Public source helpers only. Local domains are explicit; no whole P6 claim.
fn prepared_basis(limb:usize) {
 let x:u32=kani::any();let y:u32=kani::any();
 kani::assume(x<=1);kani::assume(y<0x7fff_ffff);
 let mut limbs=[0u32;8];limbs[limb]=x;
 let e=E::from_limbs(limbs).unwrap();
 let scalar=K{c0:CM31{a:M31(y),b:M31(0)},c1:CM31::ZERO};
 let mut d=fast_pairing::EbyKDot::new();assert!(d.push(e,scalar).is_ok());
 assert_eq!(d.finish(),e.mul_qm31(scalar));kani::cover!(x==1&&y!=0);
}
#[kani::proof] #[kani::unwind(10)] fn XRl_prepared_basis_0(){prepared_basis(0);}
#[kani::proof] #[kani::unwind(10)] fn XRl_prepared_basis_1(){prepared_basis(1);}
fn prepared_frame(one:bool) {
 let x:u32=kani::any();kani::assume(x<0x7fff_ffff);
 let scalar=K{c0:CM31{a:M31(x),b:M31(0)},c1:CM31::ZERO};
 let mut d=fast_pairing::EbyKDot::new();
 let e=if one{E::ONE}else{E::ZERO};
 assert!(d.push(e,scalar).is_ok());
 assert!(d.push(E::ZERO,scalar).is_ok());
 assert_eq!(d.finish(),e.mul_qm31(scalar));kani::cover!(x!=0);
}
#[kani::proof] #[kani::unwind(10)] fn XRl_prepared_zero_frame(){prepared_frame(false);}
#[kani::proof] #[kani::unwind(10)] fn XRl_prepared_one_frame(){prepared_frame(true);}

// Split replacement after K005 whole-checkpoint timeout. These are the native
// serialization methods used by each checkpoint loop iteration, not a proof
// that the enclosing body or its three digest effects match the Lean model.
#[kani::proof] #[kani::unwind(14)] fn XRl_checkpoint_query_word(){
 let q:u32=kani::any();let prefix:[u8;8]=kani::any();
 let mut out=alloc::vec::Vec::from(prefix);
 out.extend_from_slice(&q.to_le_bytes());
 assert_eq!(out.len(),12);assert_eq!(&out[..8],&prefix);
 assert_eq!(&out[8..12],&[q as u8,(q>>8) as u8,(q>>16) as u8,(q>>24) as u8]);
 kani::cover!(q==0xffff_ffff);
}
#[kani::proof] #[kani::unwind(18)] fn XRl_checkpoint_scalar_bytes(){
 let xs:[u32;4]=kani::any();for x in xs{kani::assume(x<0x7fff_ffff);}
 let k=K{c0:CM31{a:M31(xs[0]),b:M31(xs[1])},c1:CM31{a:M31(xs[2]),b:M31(xs[3])}};
 let mut bs=[0u8;16];k.write_le_bytes(&mut bs);
 for j in 0..4 {assert_eq!(&bs[4*j..4*j+4],&xs[j].to_le_bytes());}
 assert_eq!(K::from_le_bytes(&bs),Some(k));kani::cover!(xs[3]!=0);
}
#[kani::proof] #[kani::unwind(34)] fn XRl_checkpoint_wide_bytes(){
 let xs:[u32;8]=kani::any();for x in xs{kani::assume(x<0x7fff_ffff);}
 let e=E::from_limbs(xs).unwrap();let bs=e.to_le_bytes();
 for j in 0..8 {assert_eq!(&bs[4*j..4*j+4],&xs[j].to_le_bytes());}
 assert_eq!(E::from_le_bytes(&bs),Some(e));kani::cover!(xs[7]!=0);
}
#[kani::proof] #[kani::unwind(18)] fn XRl_checkpoint_next(){
 let next:usize=kani::any();let mut out=alloc::vec::Vec::from(*b"R1P2CKP2");
 out.extend_from_slice(&[2,next as u8,1,0,0,0,0,0]);
 assert_eq!(out.len(),16);assert_eq!(out[9],(next%256) as u8);
 assert_eq!(&out[..8],b"R1P2CKP2");kani::cover!(next>255);
}
#[kani::proof] fn XRl_checkpoint_layout(){
 use aspis_r1_cost_probe::{verifier,transport::Variant};
 let n:u8=kani::any();kani::assume(n<3);
 let v=match n{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};
 assert_eq!(verifier::CHECKPOINT_FIXED,744);
 assert_eq!(verifier::checkpoint_size(v),712+16*v.final_len()+32);
 assert_eq!(verifier::checkpoint_size(v),if n==0{4840}else{1768});
 kani::cover!(n==0);kani::cover!(n==1);kani::cover!(n==2);
}
