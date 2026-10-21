#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use aspis_s126_owned_sdk::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk,LiveGuards,
 owned_acquire_shared,owned_acquire_checkpoint,owned_release_guards,owned_data_len};
#[cfg(kani)] mod proofs {
use super::*;

fn native_counts(counters:&[*const std::cell::Cell<isize>;3])->[isize;3] {
 [unsafe{(*counters[0]).get()},unsafe{(*counters[1]).get()},unsafe{(*counters[2]).get()}]
}
fn model_counts(model:&OwnedSdk)->[isize;3] {
 [model.data_cells[0].borrowed,model.data_cells[1].borrowed,model.data_cells[2].borrowed]
}
fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,checkpoint:Vec<u8>)->Result<(),ProgramError> {
    if checkpoint.len() != checkpoint_data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint_data.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    {
    msg!("r1:pool-adapter-stage1-checkpoint-written");
    solana_program::log::sol_log_compute_units();
    }
    Ok(())
}
fn owned_finish(sdk:&mut OwnedSdk,checkpoint:OwnedAccount,result:Vec<u8>)->Result<(),ProgramError> {
 if result.len()!=sdk.data_cells[checkpoint.data_slot].bytes.len() {return Err(ProgramError::InvalidAccountData);}
 // Owned heap bytes, not an SDK slice descriptor or pointer, are replaced.
 // The actual SDK copy/write frame is a separate concrete operation certificate.
 sdk.data_cells[checkpoint.data_slot].bytes=result;
 Ok(())
}
fn native_chain(accounts:&[AccountInfo<'_>],reply:Vec<u8>,counters:&[*const std::cell::Cell<isize>;3],trace:&mut Vec<[isize;3]>)->Result<(),ProgramError> {
 let mut checkpoint_data=accounts[2].try_borrow_mut_data()?;
 trace.push(native_counts(counters));
 let public_data=accounts[1].try_borrow_data()?;
 trace.push(native_counts(counters));
 let proof_data=accounts[0].try_borrow_data()?;
 trace.push(native_counts(counters));
 let result=native_finish(&mut checkpoint_data,reply);
 let _=(public_data.len(),proof_data.len());
 result
}
fn model_chain(model:&mut OwnedSdk,reply:Vec<u8>,trace:&mut Vec<[isize;3]>)->(Result<(),ProgramError>,LiveGuards) {
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 let status=(||{
  let checkpoint=model.accounts[2];
  owned_acquire_checkpoint(model,&mut guards,checkpoint.data_slot)?;
  trace.push(model_counts(model));
  let public_slot=model.accounts[1].data_slot;
  owned_acquire_shared(model,public_slot)?;guards.public=Some(public_slot);
  trace.push(model_counts(model));
  let proof_slot=model.accounts[0].data_slot;
  owned_acquire_shared(model,proof_slot)?;guards.proof=Some(proof_slot);
  trace.push(model_counts(model));
  owned_finish(model,checkpoint,reply)
 })();
 (status,guards)
}

#[kani::proof] #[kani::unwind(40)]
fn actual_finish_join() {
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;
 let [ref mut l0,ref mut l1,ref mut l2]=amounts;
 let mut b0:[u8;1768]=kani::any();let mut b1:[u8;1768]=kani::any();let mut b2:[u8;1768]=kani::any();
 let lengths:[usize;3]=kani::any();for length in lengths {kani::assume(length<=1768);}
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
 let selected:usize=kani::any();kani::assume(selected<3);let slot=model.accounts[selected].data_slot;
 let reply_bytes:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let reply=reply_bytes[..reply_len].to_vec();
 let mut expected_trace=Vec::new();let mut actual_trace=Vec::new();
 let (expected,guards)=model_chain(&mut model,reply.clone(),&mut expected_trace);owned_release_guards(&mut model,guards);
 let actual=native_chain(&accounts,reply,&counters,&mut actual_trace);
 assert_eq!(actual_trace.len(),expected_trace.len());
 for i in 0..actual_trace.len() {for row in 0..3 {assert_eq!(actual_trace[i][row],expected_trace[i][row]);}}
 assert!(matches!((&actual,&expected),
  (Ok(()),Ok(()))|
  (Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))|
  (Err(ProgramError::AccountAlreadyInitialized),Err(ProgramError::AccountAlreadyInitialized))|
  (Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))|
  (Err(ProgramError::InvalidInstructionData),Err(ProgramError::InvalidInstructionData))));
 kani::cover!(actual.is_ok()&&reply_len==1768,"complete SDK copy then guard drops");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidAccountData)),"length rejection then guard drops");
 kani::cover!(actual.is_ok()&&data_slots[0]==data_slots[1],"shared readonly aliases with independent checkpoint");
 let observed_slot:usize=kani::any();kani::assume(observed_slot<3);
 if lengths[observed_slot]>0 {
  let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);
  // Obtain the pointer from the retained SDK cell after all source guards drop.
  let pointer=unsafe{(**data_roots[observed_slot].as_ptr()).as_ptr()};
  assert_eq!(unsafe{*pointer.add(observed)},model.data_cells[observed_slot].bytes[observed]);
 }
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
 kani::cover!(initial_counts[slot]==isize::MAX,"saturated shared borrow rejects");
 kani::cover!(initial_counts[slot]==0,"ordinary borrow succeeds");
}
}
