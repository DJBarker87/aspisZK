#!/usr/bin/env python3
from pathlib import Path
import sys,hashlib,json
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s=r'''#![allow(dead_code)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
#[cfg(kani)] mod proofs {
 use super::*;
 fn shared_snapshot<const N:usize>() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let mut lamports=kani::any();let before_lamports=lamports;
  let mut bytes:[u8;N]=kani::any();let selected:usize=kani::any();kani::assume(selected<N);
  let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());
  let alias=account.clone();
  let data=account.try_borrow_data().unwrap();
  let second=alias.try_borrow_data().unwrap();
  let snapshot=data.to_vec();
  assert_eq!(snapshot.len(),N);assert_eq!(snapshot[selected],data[selected]);
  assert_eq!(snapshot[selected],second[selected]);
  assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
  drop(second);drop(data);
  assert_eq!(account.try_borrow_data().unwrap()[selected],snapshot[selected]);
  assert_eq!(**account.try_borrow_lamports().unwrap(),before_lamports);
  assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(snapshot[selected]!=0,"arbitrary nonzero snapshot byte");
 }
 #[kani::proof] #[kani::unwind(3)]
 fn public_owned_snapshot_actual_sdk() {shared_snapshot::<1880>();}
 #[kani::proof] #[kani::unwind(3)]
 fn proof_owned_snapshot_actual_sdk() {shared_snapshot::<58295>();}
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-read-snapshots"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification='Actual SDK immutable AccountInfo borrow, full arbitrary bytes at admitted sizes1880/58295, owned-copy pointwise equality at any selected index, metadata arbitrary, immutable alias coexistence/exclusive conflict and release. Each selected index is arbitrary, so every cell is covered. Allocation failure is not modeled by Kani; retain runtime abort boundary P2.'),indent=2)+'\n')
