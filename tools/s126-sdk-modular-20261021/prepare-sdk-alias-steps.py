#!/usr/bin/env python3
"""Concrete SDK alias/borrow steps, no parser or whole-stage loop."""
from pathlib import Path
import json,hashlib,sys
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s='''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn shared_alias_exact_view() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports:kani::ArbitraryMarker=unreachable!();
 }
}
'''
# Keep the real SDK structs and every byte, without executing a long byte loop.
s=s.replace('let mut lamports:kani::ArbitraryMarker=unreachable!();','''let mut lamports=0;let mut storage:[u8;58295]=kani::any();
  let length:usize=kani::any();kani::assume(length<=58295);
  let original=AccountInfo::new(&key,false,false,&mut lamports,&mut storage[..length],&owner,false,0);
  let alias=original.clone();
  let first=original.try_borrow_data().unwrap();let second=alias.try_borrow_data().unwrap();
  assert_eq!(first.len(),second.len());assert_eq!(first.as_ptr(),second.as_ptr());
  assert!(first.len()!=1880 || second.len()!=58295);
  if length>0 {let selected:usize=kani::any();kani::assume(selected<length);assert_eq!(first[selected],second[selected]);}
  drop(second);drop(first);assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(length==1880,"public sized alias");kani::cover!(length==58295,"proof sized alias");''')
pos=s.rindex('\n}')
s=s[:pos]+'''
 #[kani::proof]
 #[kani::unwind(3)]
 fn exclusive_guard_blocks_alias() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut storage:[u8;58295]=kani::any();
  let length:usize=kani::any();kani::assume(length<=58295);
  let original=AccountInfo::new(&key,false,true,&mut lamports,&mut storage[..length],&owner,false,0);
  let alias=original.clone();
  let guard=original.try_borrow_mut_data().unwrap();
  assert!(matches!(alias.try_borrow_data(),Err(ProgramError::AccountBorrowFailed)));
  assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
  assert_eq!(guard.len(),length);
  drop(guard);assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(length==1768,"live checkpoint guard");
 }
'''+s[pos:]
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-alias-steps"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='Real SDK cloned Rc/RefCell data handles; all lengths0..58295 and all byte values. Conditional accepted adapter widths exclude shared public/proof storage. Exclusive checkpoint guard excludes input aliases. This is a leaf SDK certificate, not a whole-stage proof or an arbitrary-capacity RefCell counter theorem.'),indent=2)+'\n')
