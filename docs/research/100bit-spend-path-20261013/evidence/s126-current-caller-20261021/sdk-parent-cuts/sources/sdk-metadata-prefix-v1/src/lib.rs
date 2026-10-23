#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use aspis_s126_owned_sdk::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk,LiveGuards,
 owned_acquire_shared,owned_acquire_checkpoint,owned_release_guards,owned_data_len};
#[cfg(kani)] mod proofs {
use super::*;
use solana_program::entrypoint::ProgramResult;
use aspis_r1_cost_probe::{verifier,transport::Variant};
fn readonly_buffer_meta_ok(
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_readonly_buffer(account: &AccountInfo<'_>) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn require_verifier_checkpoint(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    writable: bool,
) -> ProgramResult {
    if account.owner != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.try_data_len()? != verifier::checkpoint_size(Variant::S2)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_distinct_accounts<const N: usize>(accounts: &[&AccountInfo<'_>; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}
fn native_metadata_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    require_distinct_accounts(&[proof_account, public_account, checkpoint_account])?;
    require_readonly_buffer(proof_account)?;
    require_readonly_buffer(public_account)?;
    require_verifier_checkpoint(checkpoint_account, program_id, true)?;
    Ok(())
}
fn owned_metadata_prefix(program_id:[u8;32],sdk:&OwnedSdk,data:&[u8])->ProgramResult {
 if !(data == &[3,10] || data == &[3,11]) || sdk.accounts.len()!=3 {
  return Err(ProgramError::InvalidInstructionData);
 }
 let proof=sdk.accounts[0];let public=sdk.accounts[1];let checkpoint=sdk.accounts[2];
 // Exact three-key comparison order of require_distinct_accounts on 3 inputs.
 if proof.key==public.key || proof.key==checkpoint.key || public.key==checkpoint.key {
  return Err(ProgramError::InvalidArgument);
 }
 if proof.is_signer || proof.is_writable || proof.executable {return Err(ProgramError::InvalidAccountData);}
 if public.is_signer || public.is_writable || public.executable {return Err(ProgramError::InvalidAccountData);}
 if checkpoint.owner!=program_id || checkpoint.is_signer || checkpoint.executable
  || !checkpoint.is_writable || owned_data_len(sdk,checkpoint.data_slot)?!=verifier::checkpoint_size(Variant::S2) {
  return Err(ProgramError::InvalidAccountData);
 }
 Ok(())
}
#[kani::proof] #[kani::unwind(40)]
fn metadata_prefix_join() {
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;
 let [ref mut l0,ref mut l1,ref mut l2]=amounts;
 let mut b0:[u8;10485760]=kani::any();let mut b1:[u8;10485760]=kani::any();let mut b2:[u8;10485760]=kani::any();
 let lengths:[usize;3]=kani::any();for length in lengths {kani::assume(length<=10485760);}
 let pointers=[b0.as_ptr(),b1.as_ptr(),b2.as_ptr()];
 let snapshots=[b0[..lengths[0]].to_vec(),b1[..lengths[1]].to_vec(),b2[..lengths[2]].to_vec()];
 let mut accounts=[
 AccountInfo::new(&keys[0],flags[0][0],flags[0][1],l0,&mut b0[..lengths[0]],&owners[0],flags[0][2],rents[0]),
 AccountInfo::new(&keys[1],flags[1][0],flags[1][1],l1,&mut b1[..lengths[1]],&owners[1],flags[1][2],rents[1]),
 AccountInfo::new(&keys[2],flags[2][0],flags[2][1],l2,&mut b2[..lengths[2]],&owners[2],flags[2][2],rents[2]),
 ];
 let data_roots=[accounts[0].data.clone(),accounts[1].data.clone(),accounts[2].data.clone()];
 let lamport_roots=[accounts[0].lamports.clone(),accounts[1].lamports.clone(),accounts[2].lamports.clone()];
 let data_slots:[usize;3]=kani::any();let lamport_slots:[usize;3]=kani::any();
 for i in 0..3 {
  kani::assume(data_slots[i]<3);kani::assume(lamport_slots[i]<3);
  accounts[i].data=data_roots[data_slots[i]].clone();
  accounts[i].lamports=lamport_roots[lamport_slots[i]].clone();
 }
 let initial_counts:[isize;3]=kani::any();let initial_lamport_counts:[isize;3]=kani::any();
 let counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&data_roots[i]).cast::<std::cell::Cell<isize>>());
 let lamport_counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<std::cell::Cell<isize>>());
 for i in 0..3 {
  assert_eq!(unsafe{(*counters[i]).get()},0);assert_eq!(unsafe{(*lamport_counters[i]).get()},0);
  unsafe{(*counters[i]).set(initial_counts[i]);(*lamport_counters[i]).set(initial_lamport_counts[i]);}
 }
 let mut model=OwnedSdk{
  accounts:(0..3).map(|i|OwnedAccount{key:keys[i].to_bytes(),owner:owners[i].to_bytes(),is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:data_slots[i],lamports_slot:lamport_slots[i]}).collect(),
  data_cells:snapshots.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:initial_counts[i],strong:std::rc::Rc::strong_count(&data_roots[i]),weak:std::rc::Rc::weak_count(&data_roots[i])}).collect(),
  lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:initial_amounts[i],borrowed:initial_lamport_counts[i],strong:std::rc::Rc::strong_count(&lamport_roots[i]),weak:std::rc::Rc::weak_count(&lamport_roots[i])}).collect(),
 };
 for i in 0..3 {
  assert_eq!(model.accounts[i].key,accounts[i].key.to_bytes());assert_eq!(model.accounts[i].owner,accounts[i].owner.to_bytes());
  assert_eq!(model.accounts[i].is_signer,accounts[i].is_signer);assert_eq!(model.accounts[i].is_writable,accounts[i].is_writable);
  assert_eq!(model.accounts[i].executable,accounts[i].executable);assert_eq!(model.accounts[i].rent_epoch,accounts[i].rent_epoch);
  assert!(std::rc::Rc::ptr_eq(&accounts[i].data,&data_roots[model.accounts[i].data_slot]));
  assert!(std::rc::Rc::ptr_eq(&accounts[i].lamports,&lamport_roots[model.accounts[i].lamports_slot]));
 }
 let program=Pubkey::new_from_array(kani::any());
 let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);
 let actual=native_metadata_prefix(&program,&accounts,&instruction[..instruction_len]);
 let expected=owned_metadata_prefix(program.to_bytes(),&model,&instruction[..instruction_len]);
 assert_eq!(actual,expected);
 kani::cover!(actual.is_ok(),"all original metadata checks pass");
 kani::cover!(matches!(actual,Err(ProgramError::AccountBorrowFailed)),"exact checkpoint size borrow failure");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidArgument)),"exact duplicate-key rejection");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidInstructionData)),"exact instruction rejection");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidAccountData)),"exact metadata rejection");
 for i in 0..3 {
  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);assert_eq!(model.data_cells[i].borrowed,initial_counts[i]);
  assert_eq!(unsafe{(*lamport_counters[i]).get()},initial_lamport_counts[i]);assert_eq!(model.lamports_cells[i].borrowed,initial_lamport_counts[i]);
  assert_eq!(model.lamports_cells[i].amount,initial_amounts[i]);
  assert_eq!(model.data_cells[i].strong,std::rc::Rc::strong_count(&data_roots[i]));assert_eq!(model.data_cells[i].weak,std::rc::Rc::weak_count(&data_roots[i]));
  assert_eq!(model.lamports_cells[i].strong,std::rc::Rc::strong_count(&lamport_roots[i]));assert_eq!(model.lamports_cells[i].weak,std::rc::Rc::weak_count(&lamport_roots[i]));
  assert_eq!(model.data_cells[i].bytes.len(),lengths[i]);
 }
 // Restore injected logical counters before SDK handle destruction.
 for i in 0..3 {unsafe{(*counters[i]).set(0);(*lamport_counters[i]).set(0);}}
 kani::cover!(data_slots[0]==data_slots[1]&&data_slots[1]==data_slots[2],"all account data handles alias");
 kani::cover!(data_slots[0]!=data_slots[1]&&data_slots[0]!=data_slots[2]&&data_slots[1]!=data_slots[2],"all account data handles distinct");
 kani::cover!(lamport_slots[0]==lamport_slots[1]&&data_slots[0]!=data_slots[1],"lamports alias independently of data");
 kani::cover!(initial_counts[0]==isize::MAX,"saturated shared borrow rejects");
 kani::cover!(initial_counts[0]==0,"ordinary borrow succeeds");
}
}
