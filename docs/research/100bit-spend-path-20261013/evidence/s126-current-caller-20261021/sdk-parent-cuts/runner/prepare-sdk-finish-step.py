#!/usr/bin/env python3
"""One symbolic SDK byte-assignment step and exact write set, for loop composition.
This candidate is not the frozen whole-copy implementation. The count/loop
induction and actual frozen complete-copy correspondence remain explicit obligations.
"""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s=r'''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
#[cfg_attr(kani,kani::requires(destination.len()==1768 && source.len()==1768))]
#[cfg_attr(kani,kani::requires(offset<1768))]
#[cfg_attr(kani,kani::requires(target==unsafe{destination.as_mut_ptr().add(offset)}))]
#[cfg_attr(kani,kani::modifies(target))]
#[cfg_attr(kani,kani::ensures(|_| destination[offset]==old(source[offset])))]
fn native_copy_step(destination:&mut std::cell::RefMut<'_,&mut [u8]>,source:&[u8],offset:usize,target:*mut u8) {
 destination[offset]=source[offset];
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_copy_step)] #[kani::unwind(8)]
 fn actual_sdk_copy_step_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let source:[u8;1768]=kani::any();
  let offset:usize=kani::any();kani::assume(offset<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let target=unsafe{guard.as_mut_ptr().add(offset)};
  native_copy_step(&mut guard,&source,offset,target);
  kani::cover!(offset==0,"first actual SDK copy step");
  kani::cover!(offset==1767,"last actual SDK copy step");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-finish-step"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='Actual SDK RefMut over arbitrary1768-byte contents, arbitrary1768 source bytes, symbolic offset0..1768, metadata and lamports arbitrary. Ghost target pointer is required equal to the actual SDK destination pointer plus offset. Frame permits only that one destination byte; no other SDK field/counter/header is in the modifies set.',remaining='Compile/check contract and audit actual assigns/ensures; compose count induction and exact frozen whole-copy/native reference correspondence, then parent state transport.'),indent=2)+'\n')
