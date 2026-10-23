#!/usr/bin/env python3
"""Three-account/two-heap alias construction and one real SDK operation.
All metadata/heap fields are retained; this is not a whole-stage replacement.
"""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'shared';assert mode in ['shared','exclusive','length','chain'];limit=int(sys.argv[3]) if len(sys.argv)>3 else 58295
assert 0<limit<=10*1024*1024
(O/'src').mkdir(exist_ok=True,parents=True)
s=r'''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use aspis_s126_owned_sdk::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk,LiveGuards,
 owned_acquire_shared,owned_acquire_checkpoint,owned_release_guards,owned_data_len};
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof] #[kani::unwind(40)]
fn three_account_heap_shared_join() {
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;
 let [ref mut l0,ref mut l1,ref mut l2]=amounts;
 let mut b0:[u8;58295]=kani::any();let mut b1:[u8;58295]=kani::any();let mut b2:[u8;58295]=kani::any();
 let lengths:[usize;3]=kani::any();for length in lengths {kani::assume(length<=58295);}
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
 let expected=owned_acquire_shared(&mut model,slot);
 let actual=accounts[selected].try_borrow_data();
 match actual {
  Ok(guard)=>{
   assert!(expected.is_ok());assert_eq!(guard.len(),model.data_cells[slot].bytes.len());
   assert_eq!(guard.as_ptr(),pointers[slot]);
   for i in 0..3 {assert_eq!(unsafe{(*counters[i]).get()},model.data_cells[i].borrowed);}
   drop(guard);owned_release_guards(&mut model,LiveGuards{checkpoint:None,public:Some(slot),proof:None});
  },
  Err(error)=>{assert!(matches!(error,ProgramError::AccountBorrowFailed));assert!(matches!(expected,Err(ProgramError::AccountBorrowFailed)));},
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
'''
if mode=='chain':
 s=s.replace('fn three_account_heap_shared_join()', 'fn three_account_heap_chain_join()')
 helpers=r"""
fn native_counts(counters:&[*const std::cell::Cell<isize>;3])->[isize;3] {
 [unsafe{(*counters[0]).get()},unsafe{(*counters[1]).get()},unsafe{(*counters[2]).get()}]
}
fn model_counts(model:&OwnedSdk)->[isize;3] {
 [model.data_cells[0].borrowed,model.data_cells[1].borrowed,model.data_cells[2].borrowed]
}
fn native_chain(accounts:&[AccountInfo<'_>],cut:u8,counters:&[*const std::cell::Cell<isize>;3],trace:&mut Vec<[isize;3]>)->Result<(),ProgramError> {
 let proof_account=&accounts[0];let public_account=&accounts[1];let checkpoint_account=&accounts[2];
 let checkpoint_data=checkpoint_account.try_borrow_mut_data()?;
 trace.push(native_counts(counters));
 if cut==0 {return Err(ProgramError::AccountAlreadyInitialized);}
 let public_data=public_account.try_borrow_data()?;
 trace.push(native_counts(counters));
 if cut==1 {return Err(ProgramError::InvalidAccountData);}
 let proof_data=proof_account.try_borrow_data()?;
 trace.push(native_counts(counters));
 if cut==2 {return Err(ProgramError::InvalidAccountData);}
 if cut==3 {return Err(ProgramError::InvalidInstructionData);}
 // Read the guarded descriptors at the final point; no byte loop is cut here.
 let _=(checkpoint_data.len(),public_data.len(),proof_data.len());
 Ok(())
}
fn model_chain(model:&mut OwnedSdk,cut:u8,trace:&mut Vec<[isize;3]>)->(Result<(),ProgramError>,LiveGuards) {
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 let status=(||{
  let checkpoint_slot=model.accounts[2].data_slot;
  owned_acquire_checkpoint(model,&mut guards,checkpoint_slot)?;
  trace.push(model_counts(model));
  if cut==0 {return Err(ProgramError::AccountAlreadyInitialized);}
  let public_slot=model.accounts[1].data_slot;
  owned_acquire_shared(model,public_slot)?;guards.public=Some(public_slot);
  trace.push(model_counts(model));
  if cut==1 {return Err(ProgramError::InvalidAccountData);}
  let proof_slot=model.accounts[0].data_slot;
  owned_acquire_shared(model,proof_slot)?;guards.proof=Some(proof_slot);
  trace.push(model_counts(model));
  if cut==2 {return Err(ProgramError::InvalidAccountData);}
  if cut==3 {return Err(ProgramError::InvalidInstructionData);}
  Ok(())
 })();
 (status,guards)
}
"""
 s=s.replace('use super::*;\n#[kani::proof]', 'use super::*;\n'+helpers+'\n#[kani::proof]')
 a=s.index(' let expected=owned_acquire_shared(&mut model,slot);');b=s.index(' for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);',a)
 s=s[:a]+r""" let cut:u8=kani::any();kani::assume(cut<5);
 let mut expected_trace=Vec::new();let mut actual_trace=Vec::new();
 let (expected,guards)=model_chain(&mut model,cut,&mut expected_trace);owned_release_guards(&mut model,guards);
 let actual=native_chain(&accounts,cut,&counters,&mut actual_trace);
 assert_eq!(actual_trace.len(),expected_trace.len());
 for i in 0..actual_trace.len() {for row in 0..3 {assert_eq!(actual_trace[i][row],expected_trace[i][row]);}}
 assert!(matches!((&actual,&expected),
  (Ok(()),Ok(()))|
  (Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))|
  (Err(ProgramError::AccountAlreadyInitialized),Err(ProgramError::AccountAlreadyInitialized))|
  (Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))|
  (Err(ProgramError::InvalidInstructionData),Err(ProgramError::InvalidInstructionData))));
 kani::cover!(actual.is_ok(),"all three live guards return success");
 kani::cover!(matches!(actual,Err(ProgramError::AccountAlreadyInitialized)),"return after checkpoint guard");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidAccountData))&&cut==1,"return after public guard");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidInstructionData)),"return after proof guard");
"""+s[b:]
if mode=='exclusive':
 s=s.replace('three_account_heap_shared_join','three_account_heap_exclusive_join')
 s=s.replace('let expected=owned_acquire_shared(&mut model,slot);','let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};let expected=owned_acquire_checkpoint(&mut model,&mut guards,slot);')
 s=s.replace('accounts[selected].try_borrow_data()','accounts[selected].try_borrow_mut_data()')
 s=s.replace('owned_release_guards(&mut model,LiveGuards{checkpoint:None,public:Some(slot),proof:None})','owned_release_guards(&mut model,guards)')
elif mode=='length':
 s=s.replace('three_account_heap_shared_join','three_account_heap_length_join')
 s=s.replace('let expected=owned_acquire_shared(&mut model,slot);','let expected=owned_data_len(&model,slot);')
 s=s.replace('let actual=accounts[selected].try_borrow_data();','let actual=accounts[selected].try_data_len();')
 a=s.index('  Ok(guard)=>{');b=s.index('  Err(error)=>',a)
 s=s[:a]+'''  Ok(length)=>{assert!(expected.is_ok());assert_eq!(expected.unwrap(),length);assert_eq!(length,lengths[slot]);},
'''+s[b:]
s=s.replace('58295',str(limit))
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-heap-MODE-join"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-s126-owned-sdk={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/owned-sdk-v3"}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('MODE',mode))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),mode=mode,max_buffer_bytes=limit,qualification=__doc__,domain=('Three real AccountInfo values, independent arbitrary metadata, arbitrary data/lamport slot maps into three concrete Rc/RefCell roots, every signed data/lamport counter, buffer lengths0..58295 and all byte values. '+('The three source-order borrow points are retained; child computations are represented only by return-phase cuts. This is a lifecycle cut, not the complete stage1.' if mode=='chain' else 'Selected operation is arbitrary account0..2. This is a one-operation join, not the complete stage1.')+' Rc strong/weak counts are those of the constructed alias graph; reuse independent wider write-frame certificates separately. No unrestricted account-length theorem.').replace('58295',str(limit))),indent=2)+'\n')
