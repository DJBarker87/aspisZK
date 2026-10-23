#![allow(dead_code,unexpected_cfgs)]
use solana_program::program_error::ProgramError;
use aspis_r1_cost_probe::{verifier,transport::Variant};
use aspis_statement::pool_v1::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;

pub fn native_gate(proof_data:&std::cell::Ref<'_,&mut [u8]>,candidate:[u8;688])->Result<(usize,usize),ProgramError> {
    let proof_length = verifier::PROOF_BYTES;
    let proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start.checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_data.len() != proof_end
        || proof_data[..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((proof_start,proof_end))
}

pub fn prefix_different(bytes:&[u8],candidate:&[u8])->bool {
 if bytes.len()<candidate.len() {return true;}
 let mut offset=0;
 while offset<candidate.len() {
  if bytes[offset]!=candidate[offset] {return true;}
  offset+=1;
 }
 false
}

pub fn reference_gate(proof_data:&[u8],candidate:&[u8;688])->Result<(usize,usize),ProgramError> {
 let proof_length=57607usize;
 let proof_start=688usize;
 let proof_end=proof_start.checked_add(proof_length).ok_or(ProgramError::InvalidAccountData)?;
 if proof_data.len()!=proof_end {return Err(ProgramError::InvalidAccountData);}
 if prefix_different(proof_data,candidate) {return Err(ProgramError::InvalidAccountData);}
 if proof_data[proof_start+8]!=2 {return Err(ProgramError::InvalidAccountData);}
 Ok((proof_start,proof_end))
}

#[cfg(kani)] mod proofs {
 use super::*;
 use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
 #[kani::proof] #[kani::unwind(8)]
 fn actual_sdk_guard_other_lengths() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;10485760]=kani::any();let candidate:[u8;688]=kani::any();
  let length:usize=kani::any();kani::assume(length<=10485760);kani::assume(length!=58295);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes[..length],&owner,flags[2],rent);
  let data=account.try_borrow_data().unwrap();
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<std::cell::Cell<isize>>();
  let before=unsafe{(*counter).get()};let pointer=data.as_ptr();
  let actual=native_gate(&data,candidate);
  assert_eq!(actual,Err(ProgramError::InvalidAccountData));
  assert_eq!(data.as_ptr(),pointer);assert_eq!(data.len(),length);
  assert_eq!(unsafe{(*counter).get()},before);
  kani::cover!(length==10485760,"maximum runtime buffer rejects without scanning");
  kani::cover!(length==0,"empty runtime buffer rejects without scanning");
 }
}
