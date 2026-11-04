from pathlib import Path
import json,subprocess
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;I=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text());P='programs/r1-cost-probe/src/'
a=I[P+'NFU_owned.rs'];a+='''
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_len_reply(){let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn verifier_checkpoint_reply(){let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact != cfg!(NFU_invert));}
'''
lib=subprocess.check_output(['git','show','4bb3b3f:'+P+'lib.rs'],text=True);update({P+'NFU_owned.rs':a,P+'lib.rs':'#![cfg_attr(kani,feature(allocator_api))]\n'+lib},'NFU_meta_tail')
items=[];index=74
for g in list(range(1,8))+list(range(9,14)):
 for e in [0,1]:items.append(dict(attempt=f'NFU_K{index:03}',kind='kani',target=f'verifier::NFU_verifier::finish_g{g:02}',exit=e,env={'NFU_INVERT':'1'}if e else {}));index+=1
assert index==98
for i,t,e in [(98,'data_len_reply',0),(99,'data_len_reply',1),(100,'verifier_checkpoint_reply',0),(51,'verifier_checkpoint_reply',1)]:items.append(dict(attempt=f'NFU_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NFU_owned::'+t,exit=e,env={'NFU_PROGRAM':'1',**({'NFU_INVERT':'1'}if e else {})}))
(E/'NFU_QUEUE_REMAINDER.json').write_text(json.dumps(items,indent=1)+'\n')
