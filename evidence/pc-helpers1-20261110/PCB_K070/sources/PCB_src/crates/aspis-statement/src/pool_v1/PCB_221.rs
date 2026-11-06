use super::*;
pub(super) fn reference(leaf:&PoolV1PairLeafWitnessV1)->M31 { leaf.second_commitment[7] }
#[cfg(kani)]
#[kani::proof_for_contract(PoolV1PairLeafWitnessV1::second_sentinel)]
fn small_contract(){let p:PoolV1PairLeafWitnessV1=kani::any();let _=p.second_sentinel();}

#[cfg(kani)] #[kani::ensures(|_| true)]
fn record_weak(x:u32)->M31 {M31(x)}
#[cfg(kani)] #[kani::proof_for_contract(record_weak)]
fn record_weak_contract(){let _=record_weak(kani::any());}
#[cfg(kani)] #[kani::proof]
fn record_real(){let x:u32=kani::any();assert_eq!(record_weak(x).0,x);}
#[cfg(kani)] #[kani::proof] #[kani::stub_verified(record_weak)]
fn record_unimplied(){let x:u32=kani::any();assert_eq!(record_weak(x).0,x);}
#[cfg(kani)] #[kani::modifies(&mut x[0])] #[kani::ensures(|_| true)]
fn record_bad_frame(x:&mut [u32;2])->M31 {x[1]=x[1].wrapping_add(1);M31(0)}
#[cfg(kani)] #[kani::proof_for_contract(record_bad_frame)]
fn record_frame(){let mut x:[u32;2]=kani::any();let _=record_bad_frame(&mut x);}
