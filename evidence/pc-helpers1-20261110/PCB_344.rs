use super::*;
pub(super) fn reference()->() {()}
fn clear_empty(bytes:&[u8]) {assert!(bytes.is_empty());kani::cover!(bytes.is_empty(),"exact empty request reached");}
fn clear_wrong(bytes:&[u8]) {assert!(!bytes.is_empty());}
#[kani::proof_for_contract(<SolanaPairForestVerifierRuntimeV1 as PairForestVerifierRuntimeV1>::clear_return_data)]
#[kani::stub(solana_program::program::set_return_data,clear_empty)]
fn clear_contract(){let mut rt=SolanaPairForestVerifierRuntimeV1;rt.clear_return_data();}
#[kani::proof_for_contract(<SolanaPairForestVerifierRuntimeV1 as PairForestVerifierRuntimeV1>::clear_return_data)]
#[kani::stub(solana_program::program::set_return_data,clear_wrong)]
fn clear_wrong_argument(){let mut rt=SolanaPairForestVerifierRuntimeV1;rt.clear_return_data();}
#[kani::modifies(x)]
#[cfg_attr(not(PCB_NEG_UNIT),kani::ensures(|_|x[0]==0))]
#[cfg_attr(PCB_NEG_UNIT,kani::ensures(|_|x[0]!=0))]
fn unit_weak(x:&mut [u8;2]) {x[0]=0;x[1]=0;}
#[kani::proof_for_contract(unit_weak)]fn unit_contract(){let mut x:[u8;2]=kani::any();unit_weak(&mut x);}
#[kani::proof]fn unit_real(){let mut x:[u8;2]=kani::any();unit_weak(&mut x);assert_eq!(x[1],0);}
#[kani::proof]#[kani::stub_verified(unit_weak)]fn unit_unimplied(){let mut x:[u8;2]=kani::any();unit_weak(&mut x);assert_eq!(x[1],0);}
#[kani::modifies(&mut x[0])]#[kani::ensures(|_|true)]fn unit_bad_frame(x:&mut [u8;2]) {x[1]=x[1].wrapping_add(1);}
#[kani::proof_for_contract(unit_bad_frame)]fn unit_frame(){let mut x:[u8;2]=kani::any();unit_bad_frame(&mut x);}
