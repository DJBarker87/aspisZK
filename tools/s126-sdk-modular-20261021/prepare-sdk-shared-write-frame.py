#!/usr/bin/env python3
"""Actual SDK shared acquire/drop write-set contract.
Checks that the complete SDK operation writes only the signed counter cell,
so arbitrary account-buffer contents need no giant symbolic-index query.
Not a whole-stage contract or a source replacement.
"""
from pathlib import Path
import sys,json,hashlib
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
s='''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
#[cfg(kani)]
#[kani::requires(counter==std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>())]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| unsafe{(*counter).get()}==old(unsafe{(*counter).get()}))]
fn shared_roundtrip(account:&AccountInfo<'_>,counter:*const Cell<isize>) {
 match account.try_borrow_data() {
  Ok(guard)=>drop(guard),
  Err(error)=>assert!(matches!(error,ProgramError::AccountBorrowFailed)),
 }
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(shared_roundtrip)]
 #[kani::unwind(36)]
 fn actual_sdk_shared_write_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
  let mut bytes:[u8;58295]=kani::any();let length:usize=kani::any();kani::assume(length<=58295);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes[..length],&owner,flags[2],rent_epoch);
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>();
  assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_data().unwrap();assert_eq!(unsafe{(*counter).get()},1);drop(trial);
  assert_eq!(unsafe{(*counter).get()},0);
  let initial:isize=kani::any();unsafe{(*counter).set(initial);}
  shared_roundtrip(&account,counter);
  assert_eq!(unsafe{(*counter).get()},initial);
  unsafe{(*counter).set(0);}
  kani::cover!(initial==0 && length==58295,"full proof view write-set checked");
  kani::cover!(initial==isize::MAX && length==0,"saturated empty view rejection checked");
 }
}
'''
mode=sys.argv[2] if len(sys.argv)>2 else 'shared';assert mode in ['shared','exclusive']
if mode=='exclusive':
 s=s.replace('shared_roundtrip','exclusive_roundtrip').replace('actual_sdk_shared_write_frame','actual_sdk_exclusive_write_frame')
 s=s.replace('match account.try_borrow_data() {','match account.try_borrow_mut_data() {')
all_rc=len(sys.argv)>3 and sys.argv[3]=='all-rc-counts'
if all_rc:
 s=s.replace('  let counter=std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>();', '''  // The pinned RcInner header is validated before logical-count injection.
  let data_value=std::rc::Rc::as_ptr(&account.data).cast::<usize>();
  let lamport_value=std::rc::Rc::as_ptr(&account.lamports).cast::<usize>();
  let ds=unsafe{data_value.sub(2).cast_mut()};let dw=unsafe{data_value.sub(1).cast_mut()};
  let ls=unsafe{lamport_value.sub(2).cast_mut()};let lw=unsafe{lamport_value.sub(1).cast_mut()};
  assert_eq!(unsafe{*ds},1);assert_eq!(unsafe{*dw},1);assert_eq!(unsafe{*ls},1);assert_eq!(unsafe{*lw},1);
  let rc_counts:[usize;4]=kani::any();
  for count in rc_counts {kani::assume(count>=1 && count<=isize::MAX as usize);}
  unsafe{*ds=rc_counts[0];*dw=rc_counts[1];*ls=rc_counts[2];*lw=rc_counts[3];}
  assert_eq!(std::rc::Rc::strong_count(&account.data),rc_counts[0]);
  assert_eq!(std::rc::Rc::weak_count(&account.data),rc_counts[1]-1);
  assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc_counts[2]);
  assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc_counts[3]-1);
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>();''')
 s=s.replace('  unsafe{(*counter).set(0);}', '  assert_eq!(std::rc::Rc::strong_count(&account.data),rc_counts[0]);\n  assert_eq!(std::rc::Rc::weak_count(&account.data),rc_counts[1]-1);\n  assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc_counts[2]);\n  assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc_counts[3]-1);\n  unsafe{(*counter).set(0);*ds=1;*dw=1;*ls=1;*lw=1;}')
limit=int(sys.argv[4]) if len(sys.argv)>4 else 58295
assert 0<limit<=10*1024*1024
all_lamport_counters=len(sys.argv)>5 and sys.argv[5]=='all-lamport-counters'
if all_lamport_counters:
 s=s.replace('  let initial:isize=kani::any();', """  let lamport_counter=std::rc::Rc::as_ptr(&account.lamports).cast::<Cell<isize>>();
  assert_eq!(unsafe{(*lamport_counter).get()},0);
  let initial_lamport:isize=kani::any();unsafe{(*lamport_counter).set(initial_lamport);}
  let initial:isize=kani::any();""")
 s=s.replace('  unsafe{(*counter).set(0);', """  assert_eq!(unsafe{(*lamport_counter).get()},initial_lamport);
  unsafe{(*lamport_counter).set(0);}
  unsafe{(*counter).set(0);""")
s=s.replace('58295',str(limit))
if limit!=58295:s=s.replace('full proof view write-set checked','maximum buffer view write-set checked')
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-shared-write-frame"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),max_buffer_bytes=limit,all_lamport_counters=all_lamport_counters,qualification=__doc__,mode=mode,rc_counter_domain=('Both data and lamport Rc strong counts1..isizeMAX; internal weak counts1..isizeMAX, public weak=internal-1. Compiler-layout header validated before injection.' if all_rc else 'SDK constructor counts: strong1,public weak0.'),domain=('All signed data counters, '+('all signed lamport counters, ' if all_lamport_counters else 'constructor-zero lamport counters, ')+f'full{limit}-byte symbolic storage, view length0..{limit}, every account metadata/lamport value. Compiler-specific counter location validated before injection.'),contract='Only counter.cast::<isize>() may be assigned; counter restored on return. Exact original SDK acquire and guard drop execute; acquisition mode explicitly recorded.',remaining='Need actual enclosing source composition; no whole S2 closure.'),indent=2)+'\n')
