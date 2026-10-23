#!/usr/bin/env python3
"""Actual std byte-copy primitive with fixed destination frame and a generic
inherent-method bridge. The caller remains the full frozen real SDK body.
Only reached u8/1768-byte instances may use this specialized contract.
"""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s=r'''#![allow(dead_code,unexpected_cfgs)]
#[cfg(kani)] mod proofs {
 use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
 static mut OBSERVED:usize=0;
 static mut EXPECTED:u8=0;
 fn observed()->usize {unsafe{OBSERVED}}
 fn expected()->u8 {unsafe{EXPECTED}}
 #[kani::requires(destination.len()==1768 && source.len()==1768)]
 #[kani::requires(observed()<1768)]
 #[kani::requires(expected()==source[observed()])]
 #[kani::modifies(destination.as_mut_ptr().cast::<[u8;1768]>())]
 #[kani::ensures(|_| destination[observed()]==expected())]
 fn verified_byte_copy(destination:&mut [u8],source:&[u8]) {
  destination.copy_from_slice(source);
 }
 fn copy_bridge<T:Copy>(destination:&mut [T],source:&[T]) {
  assert_eq!(core::any::type_name::<T>(),"u8","only the actual byte instance is certified");
  assert_eq!(core::mem::size_of::<T>(),1);assert_eq!(core::mem::align_of::<T>(),1);
  let destination=unsafe{core::slice::from_raw_parts_mut(destination.as_mut_ptr().cast::<u8>(),destination.len())};
  let source=unsafe{core::slice::from_raw_parts(source.as_ptr().cast::<u8>(),source.len())};
  verified_byte_copy(destination,source);
 }
 #[kani::proof_for_contract(verified_byte_copy)] #[kani::unwind(1772)]
 fn std_copy_value_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let source:[u8;1768]=kani::any();
  let offset:usize=kani::any();kani::assume(offset<1768);
  unsafe{OBSERVED=offset;EXPECTED=source[offset];}
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  verified_byte_copy(&mut guard,&source);
  kani::cover!(offset==0,"std copy first observed byte");
  kani::cover!(offset==1767,"std copy last observed byte");
 }
 #[kani::proof] #[kani::unwind(8)]
 #[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]
 #[kani::stub_verified(verified_byte_copy)]
 fn verified_inherent_bridge() {
  let source:[u8;1768]=kani::any();let mut destination:[u8;1768]=kani::any();
  let offset:usize=kani::any();kani::assume(offset<1768);
  unsafe{OBSERVED=offset;EXPECTED=source[offset];}
  destination.copy_from_slice(&source);
  assert_eq!(destination[offset],source[offset]);
  kani::cover!(offset==1767,"verified inherent byte bridge reached");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-std-copy-frame"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze='b2727acd3abf79315d18b754a260f58f4b1c6326',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,domain='Actual std slice copy with a1768-byte source/destination, all bytes and symbolic observed coordinate, destination obtained from real SDK RefMut. Exact one destination-array write set; source and ghost globals readonly. Generic bridge asserts its reached concrete type is u8 and preserves the actual full std API signature.',remaining='Prove/audit primitive contract, then verify bridge and install in unchanged complete native SDK caller. Every reached specialized instance/precondition must be checked, and full source/child/state/log joins remain open.'),indent=2)+'\n')
