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

use aspis_r1_cost_probe::{verifier::{self,Prepared,Accumulator},transport::Variant};
use aspis_core::{Digest32,circle::SecureCirclePoint};
#[derive(Clone,Copy)] struct BoundaryDigest;
impl Digest32 for BoundaryDigest {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  // Distinct domains expose proof/public/checksum order and payload framing.
  let mut out=[0u8;32];out[0]=parts.len() as u8;
  out[1]=(parts[0].len()&255) as u8;out[2]=parts[0][0];
  if parts.len()==2 {out[3]=(parts[1].len()&255) as u8;out[4]=parts[1][0];}
  out
 }
}
fn prepared()->Prepared {
 Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,
 alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],
 z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]}
}
fn accumulator()->Accumulator {Accumulator{weights:alloc::vec![K::ZERO;64],rhs:E::ZERO,power:K::ZERO,next:0}}
fn checkpoint_query(j:usize){
 let q:u32=kani::any();let mut p=prepared();p.queries[j]=q;
 let out=verifier::checkpoint(&p,&accumulator(),&[3],&[7,8],BoundaryDigest);
 let at=320+4*j;
 assert_eq!(&out[at..at+4],&q.to_le_bytes());assert_eq!(out.len(),1768);
 kani::cover!(q==0xffff_ffff);
}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_query_0(){checkpoint_query(0);}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_query_21(){checkpoint_query(21);}
fn checkpoint_scalar(j:usize){
 let x:u32=kani::any();kani::assume(x<0x7fff_ffff);
 let mut limbs=[0u32;4];limbs[j]=x;
 let k=K{c0:CM31{a:M31(limbs[0]),b:M31(limbs[1])},c1:CM31{a:M31(limbs[2]),b:M31(limbs[3])}};
 let mut p=prepared();p.rho=k;
 let out=verifier::checkpoint(&p,&accumulator(),&[3],&[7,8],BoundaryDigest);
 assert_eq!(&out[304+4*j..308+4*j],&x.to_le_bytes());kani::cover!(x!=0);
}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_scalar_0(){checkpoint_scalar(0);}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_scalar_3(){checkpoint_scalar(3);}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_next(){
 let next:usize=kani::any();let mut a=accumulator();a.next=next;
 let out=verifier::checkpoint(&prepared(),&a,&[3],&[7,8],BoundaryDigest);
 assert_eq!(out[9],next as u8);kani::cover!(next>255);
}
#[kani::proof] #[kani::unwind(66)] fn XRl_checkpoint_digest_order(){
 let a:u8=kani::any();let b:u8=kani::any();
 let out=verifier::checkpoint(&prepared(),&accumulator(),&[a],&[b,8],BoundaryDigest);
 assert_eq!(&out[16..19],&[1,1,a]);assert_eq!(&out[48..51],&[1,2,b]);
 assert_eq!(&out[1736..1741],&[2,21,85,200,82]);
 kani::cover!(a!=b);
}
