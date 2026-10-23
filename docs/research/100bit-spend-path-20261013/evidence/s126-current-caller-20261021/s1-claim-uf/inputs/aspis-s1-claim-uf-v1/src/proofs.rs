#![allow(static_mut_refs)]
use super::*;
use alloc::boxed::Box;
use aspis_core::field::{M31,CM31};
use fast_pairing::{EbyKDot,ProofQ};
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{[0;32]}}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:[[0;32];2],challenges:Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:core::array::from_fn(|_|K::ZERO),mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:[0;32],
 z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],transcript:SemanticTranscript::new(Hash,&[],&[0;32]).unwrap(),
 }
}
extern "C" {
 fn aspis_uf_raw(input:*const u32,output:*mut u64);
 fn aspis_uf_finish(input:*const u64,output:*mut u32);
 fn aspis_uf_field(input:*const u32,output:*mut u32);
 fn aspis_uf_mul(input:*const u32,output:*mut u32);
 fn aspis_uf_add(input:*const u32,output:*mut u32);
}
fn raw_words(a:[u32;4],b:[u32;4])->[u64;4] {
 let input=[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]];
 let mut output=[0;4];unsafe{aspis_uf_raw(input.as_ptr(),output.as_mut_ptr());}output
}
fn raw_leaf(a:ProofQ,b:ProofQ)->[u64;4] {raw_words(a.limbs(),b.limbs())}
fn field_leaf(bytes:&[u8],index:usize)->E {
 let offset=index*32;let frame=&bytes[offset..offset+32];
 let mut input=[0u32;8];
 for j in 0..8 {input[j]=u32::from_le_bytes([frame[j*4],frame[j*4+1],frame[j*4+2],frame[j*4+3]]);}
 let mut output=[0u32;8];unsafe{aspis_uf_field(input.as_ptr(),output.as_mut_ptr());core::mem::transmute(output)}
}
fn finish_leaf(dot:EbyKDot)->E {
 let input:[u64;9]=unsafe{core::mem::transmute(dot)};let mut output=[0u32;8];
 unsafe{aspis_uf_finish(input.as_ptr(),output.as_mut_ptr());core::mem::transmute(output)}
}
fn wide_input(a:E,b:E)->[u32;16] {
 let a:[u32;8]=unsafe{core::mem::transmute(a)};let b:[u32;8]=unsafe{core::mem::transmute(b)};
 [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7]]
}
fn mul_leaf(a:E,b:E)->E {let input=wide_input(a,b);let mut output=[0u32;8];unsafe{aspis_uf_mul(input.as_ptr(),output.as_mut_ptr());core::mem::transmute(output)}}
fn add_leaf(a:E,b:E)->E {let input=wide_input(a,b);let mut output=[0u32;8];unsafe{aspis_uf_add(input.as_ptr(),output.as_mut_ptr());core::mem::transmute(output)}}
#[kani::proof]
#[kani::unwind(128)]
fn uf_congruence_preflight() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();
 assert_eq!(raw_words(a,b),raw_words(a,b));
}
#[kani::proof]
#[kani::unwind(128)]
fn uf_last_input_negative_control() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();let mut changed=b;changed[3]^=1;
 assert_eq!(raw_words(a,b),raw_words(a,changed));
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::ProofQ::raw,raw_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
fn original_point_matches_fission() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();kani::assume(point<6);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let parts:[[u32;8];7]=kani::any();let initial:[E;7]=unsafe{core::mem::transmute(parts)};
 let mut old=initial;let mut new=initial;let y1:[u8;928]=kani::any();
 let a=original_point_step(&sem,&y1,&g,point,&mut old);
 let b=reference_point_step(&sem,&y1,&g,point,&mut new);
 assert_eq!(a,b);assert_eq!(old,new);
 if a.is_err(){assert!(matches!(a,Err(Error::Parse)));assert_eq!(old,initial);}
 kani::cover!(a.is_ok(),"all29 pushes and parts update");kani::cover!(a.is_err(),"early rejection");
 kani::cover!(a.is_ok()&&point==5,"y1 point completes");kani::cover!(a.is_err()&&point==5,"y1 scalar rejected");
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::ProofQ::raw,raw_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,mul_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::add,add_leaf)]
fn original_claim_matches_fission() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let y1:[u8;928]=kani::any();let inactive:[u32;8]=kani::any();let kappa:[u32;8]=kani::any();
 let inactive:E=unsafe{core::mem::transmute(inactive)};let kappa:E=unsafe{core::mem::transmute(kappa)};
 let a=prepared_claim(&sem,&y1,inactive,&g,kappa);let b=fission_claim(&sem,&y1,inactive,&g,kappa);
 assert_eq!(a,b);kani::cover!(a.is_ok(),"whole claim returns Ok");kani::cover!(a.is_err(),"whole claim returns Err");
}
