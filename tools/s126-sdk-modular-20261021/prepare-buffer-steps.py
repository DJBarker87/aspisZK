#!/usr/bin/env python3
"""SDK iterator/owned-copy operations; no whole-stage or parser claim."""
from pathlib import Path
import hashlib,json,sys
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s=r'''#![allow(dead_code)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn checkpoint_iterator_step_actual_sdk() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut bytes:[u8;1768]=kani::any();
  let start:usize=kani::any();kani::assume(start<=1768);
  let account=AccountInfo::new(&key,false,true,&mut lamports,&mut bytes,&owner,false,0);
  let data=account.try_borrow_mut_data().unwrap();
  let mut iter=data[start..].iter();
  let before_ptr=iter.as_slice().as_ptr();let before_len=iter.len();
  // Exactly one body step of the pinned slice::Iter<u8>::any implementation.
  let outcome=match iter.next() {None=>None,Some(byte)=>Some(*byte!=0)};
  if start==1768 {
   assert!(outcome.is_none());assert_eq!(iter.len(),0);
   assert_eq!(iter.as_slice().as_ptr(),before_ptr);
  } else {
   assert_eq!(outcome,Some(data[start]!=0));
   assert_eq!(iter.len(),before_len-1);
   assert_eq!(iter.as_slice().as_ptr(),unsafe{before_ptr.add(1)});
   assert_eq!(iter.as_slice().as_ptr(),data[start+1..].as_ptr());
   assert_eq!(iter.as_slice().len(),data[start+1..].len());
  }
  kani::cover!(start==1768,"empty iterator step");
  kani::cover!(outcome==Some(false),"zero step continues");
  kani::cover!(outcome==Some(true),"nonzero step returns");
 }
 #[kani::proof]
 #[kani::unwind(18)]
 fn zero_scan_chunk_actual_std() {
  let bytes:[u8;16]=kani::any();let length:usize=kani::any();kani::assume(length<=16);
  let actual=bytes[..length].iter().any(|byte|*byte!=0);
  let mut expected=false;let mut i=0;
  while i<length {expected=expected||bytes[i]!=0;i+=1;}
  assert_eq!(actual,expected);
  kani::cover!(actual,"nonzero chunk");kani::cover!(!actual,"zero chunk");
 }
 #[kani::proof]
 #[kani::unwind(3)]
 fn checkpoint_owned_snapshot_actual_sdk() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=kani::any();let initial_lamports=lamports;
  let mut bytes:[u8;1768]=kani::any();let selected:usize=kani::any();kani::assume(selected<1768);
  let account=AccountInfo::new(&key,false,true,&mut lamports,&mut bytes,&owner,false,0);
  let alias=account.clone();
  let data=account.try_borrow_mut_data().unwrap();
  let owned=data.to_vec();
  assert_eq!(owned.len(),1768);assert_eq!(owned[selected],data[selected]);
  assert_eq!(**account.try_borrow_lamports().unwrap(),initial_lamports);
  assert!(matches!(alias.try_borrow_data(),Err(solana_program::program_error::ProgramError::AccountBorrowFailed)));
  drop(data);
  assert_eq!(alias.try_borrow_data().unwrap()[selected],owned[selected]);
  assert!(account.try_borrow_mut_data().is_ok());
  kani::cover!(owned[selected]!=0,"arbitrary owned byte");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-buffer-steps"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification='Actual SDK and actual std iterator next, any on 0..16 byte chunks, and owned checkpoint snapshot. Per-step/chunk certificates; not yet complete shipped-stage1 equivalence. Iterator step covers all cursor positions 0..1768, all checkpoint bytes, and end/continue/return branches.'),indent=2)+'\n')
