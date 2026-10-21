#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
REV='b2727acd3abf79315d18b754a260f58f4b1c6326';path='programs/r1-cost-probe/src/r1_pool_adapter.rs';source=subprocess.check_output(['git','-C',str(R),'show',REV+':'+path],text=True)
def cut(n):
 a=source.index('fn '+n);e=source.index('{',a)+1;d=1
 while d:d+=(source[e]=='{')-(source[e]=='}');e+=1
 return source[a:e]
names=['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts']
s='''#![allow(dead_code)]
use solana_program::{account_info::AccountInfo,program_error::ProgramError,entrypoint::ProgramResult,pubkey::Pubkey};
#[derive(Clone,Copy)] enum Variant {S2}
mod verifier {
 use super::*;
 // Exact frozen CHECKPOINT_FIXED and final_len(S2) arithmetic, not a free size.
 pub fn checkpoint_size(_:Variant)->usize {16+32*3+64+32*4+16+88+160+64+32*2+16+32+16*(1024>>(2*2))}
}
'''+ '\n'.join(cut(n) for n in names)+'''
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof]
fn metadata_guards_actual_sdk() {
 let program=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let required_write:bool=kani::any();
 let mut lamports=kani::any();let mut bytes=[0u8;10*1024*1024];let length:usize=kani::any();kani::assume(length<=bytes.len());
 let account=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes[..length],&owner,executable,kani::any());
 let read=require_readonly_buffer(&account);\n assert!(matches!((read,signer||writable||executable),(Ok(()),false)|(Err(ProgramError::InvalidAccountData),true)));
 let held=if kani::any(){Some(account.try_borrow_mut_data().unwrap())}else{None};
 let expected=if owner!=program||signer||executable||writable!=required_write {Err(ProgramError::InvalidAccountData)}
  else if held.is_some(){Err(ProgramError::AccountBorrowFailed)}
  else if length!=1768 {Err(ProgramError::InvalidAccountData)}else{Ok(())};
 let actual=require_verifier_checkpoint(&account,&program,required_write);
 let can_accept=actual.is_ok();let borrow_reject=matches!(&actual,Err(ProgramError::AccountBorrowFailed));let metadata_reject=matches!(&actual,Err(ProgramError::InvalidAccountData));\n assert!(matches!((actual,expected),(Ok(()),Ok(()))|(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))|(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))));
 drop(held);assert!(account.try_borrow_mut_data().is_ok());
 kani::cover!(can_accept,"metadata guard accepts");kani::cover!(borrow_reject,"metadata guard borrow error");kani::cover!(metadata_reject,"metadata guard rejects");
}
#[kani::proof]
#[kani::unwind(40)]
fn distinct_actual_sdk() {
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));let owner=Pubkey::new_from_array(kani::any());
 let mut lamports=[0u64;3];let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 let mut b0=[];let mut b1=[];let mut b2=[];
 let a0=AccountInfo::new(&keys[0],kani::any(),kani::any(),l0,&mut b0,&owner,kani::any(),kani::any());
 let a1=AccountInfo::new(&keys[1],kani::any(),kani::any(),l1,&mut b1,&owner,kani::any(),kani::any());
 let a2=AccountInfo::new(&keys[2],kani::any(),kani::any(),l2,&mut b2,&owner,kani::any(),kani::any());
 let duplicate=keys[0]==keys[1]||keys[0]==keys[2]||keys[1]==keys[2];\n assert!(matches!((require_distinct_accounts(&[&a0,&a1,&a2]),duplicate),(Ok(()),false)|(Err(ProgramError::InvalidArgument),true)));
 assert!(matches!(require_distinct_accounts(&[&a0,&a0,&a2]),Err(ProgramError::InvalidArgument)));
 kani::cover!(duplicate,"duplicate keys reached");kani::cover!(!duplicate,"distinct keys reached");
}
}
'''

s += r"""
#[cfg(kani)] mod checkpoint_steps {
 use super::*;
 #[kani::proof]
 #[kani::unwind(1770)]
 fn zero_scan_exact_sdk() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut bytes:[u8;1768]=kani::any();
  let observed:usize=kani::any();kani::assume(observed<1768);let initial=bytes[observed];
  let account=AccountInfo::new(&key,false,true,&mut lamports,&mut bytes,&owner,false,0);
  let nonzero={let checkpoint_data=account.try_borrow_mut_data().unwrap();checkpoint_data.iter().any(|byte| *byte != 0)};
  let final_data=account.try_borrow_data().unwrap();assert_eq!(final_data[observed],initial);
  if !nonzero {assert_eq!(final_data[observed],0);}
  if initial!=0 {assert!(nonzero);}
  kani::cover!(!nonzero);
 }
 #[kani::proof]
 #[kani::unwind(1770)]
 fn copy_exact_sdk() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut bytes:[u8;1768]=kani::any();let replacement:[u8;1768]=kani::any();
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,false,true,&mut lamports,&mut bytes,&owner,false,0);
  {let mut checkpoint_data=account.try_borrow_mut_data().unwrap();checkpoint_data.copy_from_slice(&replacement);}
  assert_eq!(account.try_borrow_data().unwrap()[observed],replacement[observed]);
 }
}
"""
(O/'src/lib.rs').write_text(s);(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-guards"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
sha=lambda x:hashlib.sha256(x.encode()).hexdigest();(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=REV,source_path=path,source_sha256=sha(source),declarations={n:dict(source=cut(n),sha256=sha(cut(n))) for n in names},code_sha256=sha(s),qualification='Exact guards with actual SDK AccountInfo, including RefCell borrow conflict; all metadata and keys arbitrary. Checkpoint length domain 0..10485760; no data bytes are read by these guards. This is an explicit finite domain, not unrestricted account totality.'),indent=2)+'\n')
