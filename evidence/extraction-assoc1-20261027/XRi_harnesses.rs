use super::*;
use alloc::{boxed::Box,vec};
fn any_e()->E { let x:[u32;8]=kani::any();kani::assume(x.iter().all(|v|*v<0x7fff_ffff));E::from_limbs(x).unwrap() }
fn any_k()->K {let x:[u32;4]=kani::any();kani::assume(x.iter().all(|v|*v<0x7fff_ffff));K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
#[kani::proof] #[kani::unwind(32)] fn XRi_powers29_zero(){let a=powers::<29>(E::ZERO);let i:usize=kani::any();kani::assume(i<29);assert_eq!(a[i],if i==0 {E::ONE}else{E::ZERO});}
#[kani::proof] #[kani::unwind(32)] fn XRi_powers29_one(){let a=powers::<29>(E::ONE);let i:usize=kani::any();kani::assume(i<29);assert_eq!(a[i],E::ONE);}
#[kani::proof] #[kani::unwind(10)] fn XRi_powers7_zero(){let a=powers::<7>(E::ZERO);let i:usize=kani::any();kani::assume(i<7);assert_eq!(a[i],if i==0 {E::ONE}else{E::ZERO});}
#[kani::proof] #[kani::unwind(10)] fn XRi_powers7_one(){let a=powers::<7>(E::ONE);let i:usize=kani::any();kani::assume(i<7);assert_eq!(a[i],E::ONE);}
fn digest(_: &[&[u8]])->[u8;32] {[0;32]}
fn zero_sem()->r1_semantic::Verified<aspis_core::digest::LegacyHashFn>{
 let z=K::ZERO;
 r1_semantic::Verified{roots:[[0;32];2],challenges:aspis_r1_cost_probe::r1_wire::Challenges{lambda:z,chi:z,theta:z,zc:[z;10],mu:z,eta:z},alpha:[z;10],claims:Box::new([[z;29];3]),extra:[z;29],before_z1:[z;29],state_before_z0:[0;32],z:[aspis_core::circle::SecureCirclePoint{x:z,y:z};2],transcript:aspis_r1_cost_probe::r1_wire::SemanticTranscript::new(aspis_core::digest::LegacyHashFn(digest),&[],&[0;32]).unwrap()}
}
// The digest is an explicit arbitrary dictionary instance; prepared_claim does
// not call it. This is not a contract, stub, or oracle/whole-caller proof.
#[kani::proof] #[kani::unwind(32)] fn XRi_prepared_zero(){let sem=zero_sem();let inactive=any_e();let g=powers::<29>(E::ZERO);let y1=[0;928];let a=XRi_shipped_prepared_claim(&sem,&y1,inactive,&g,E::ZERO);assert_eq!(a,XRi_reference_prepared_claim(&sem,&y1,inactive,&g,E::ZERO));assert_eq!(a,Ok(inactive));}
#[kani::proof] #[kani::unwind(32)] fn XRi_prepared_one(){let sem=zero_sem();let inactive=any_e();let g=powers::<29>(E::ONE);let y1=[0;928];let a=XRi_shipped_prepared_claim(&sem,&y1,inactive,&g,E::ONE);assert_eq!(a,XRi_reference_prepared_claim(&sem,&y1,inactive,&g,E::ONE));assert_eq!(a,Ok(inactive));}
#[kani::proof] #[kani::unwind(36)] fn XRi_checkpoint_pair(){let xs=[any_k(),any_k()];let prefix:[u8;8]=kani::any();let mut a=prefix.to_vec();let mut b=a.clone();for x in xs {XRi_shipped_put_k(&mut a,x);XRi_reference_put_k(&mut b,x);}let i:usize=kani::any();kani::assume(i<40);assert_eq!(a.len(),40);assert_eq!(a[i],b[i]);if i<8 {assert_eq!(a[i],prefix[i]);}}
#[kani::proof] #[kani::unwind(36)] fn XRi_checkpoint_four(){let xs=[any_k(),any_k(),any_k(),any_k()];let mut a=Vec::new();let mut b=Vec::new();for x in xs {XRi_shipped_put_k(&mut a,x);XRi_reference_put_k(&mut b,x);}let i:usize=kani::any();kani::assume(i<64);assert_eq!(a.len(),64);assert_eq!(a[i],b[i]);}
#[kani::proof] #[kani::unwind(36)] fn XRi_checkpoint_e_pair(){let xs=[any_e(),any_e()];let prefix:[u8;8]=kani::any();let mut a=prefix.to_vec();let mut b=a.clone();for x in xs {XRi_shipped_put(&mut a,x);XRi_reference_put(&mut b,x);}let i:usize=kani::any();kani::assume(i<72);assert_eq!(a.len(),72);assert_eq!(a[i],b[i]);if i<8 {assert_eq!(a[i],prefix[i]);}}
#[kani::proof] #[kani::unwind(70)] fn XRi_checkpoint_zero_weights(){let mut a=vec![];for _ in 0..64 {XRi_shipped_put_k(&mut a,K::ZERO);}let i:usize=kani::any();kani::assume(i<1024);assert_eq!(a.len(),1024);assert_eq!(a[i],0);}
