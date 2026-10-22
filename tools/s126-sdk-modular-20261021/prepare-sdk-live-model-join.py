#!/usr/bin/env python3
"""Check exact original SDK versus real-guard references, not shadow guards.
The two calls start at the same account state; the actual guard is observed
and dropped before the reference call, then all live-result bits/counters,
errors and final drop effects are compared. Counter-only write frame enforced.
"""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2]
out=Path(sys.argv[1]);mode=sys.argv[2];assert mode in ['length','shared','exclusive']
(out/'src').mkdir(parents=True,exist_ok=False)
method={'length':'try_data_len','shared':'try_borrow_data','exclusive':'try_borrow_mut_data'}[mode]
base=Path(sys.argv[3])/'src/lib.rs';s=base.read_text()
limit=int(sys.argv[4]) if len(sys.argv)>4 else 10485760
assert 0<limit<=10485760
s=s.replace('10485760',str(limit))
s=s.replace('use std::cell::Cell;', 'use std::cell::Cell;\nmod sdk_live_models;')
target='''#[kani::proof_for_contract(AccountInfo::'''+method+''')] #[kani::unwind(36)]'''
assert target in s
s=s.replace(target,'''#[kani::proof_for_contract(compare_live)] #[kani::unwind(36)]''')
needle=' let result=account.'+method+'();\n drop(result);'
assert needle in s;s=s.replace(needle,' compare_live(&account,counter);')
if mode=='length':
 compare=''' let actual=account.try_data_len();
 let after_actual=unsafe{(*counter).get()};
 let expected=sdk_live_models::length(account);
 match (actual,expected) {
  (Ok(a),Ok(b))=>assert_eq!(a,b),
  (Err(a),Err(b))=>assert!(matches!(a,ProgramError::AccountBorrowFailed)&&matches!(b,ProgramError::AccountBorrowFailed)),
  _=>panic!("different SDK result constructors"),
 }
 assert_eq!(unsafe{(*counter).get()},after_actual);
'''
else:
 compare=''' let actual=account.METHOD();
 let after_actual=unsafe{(*counter).get()};
 let observed=match &actual {
  Ok(guard)=>{
   assert_eq!(std::mem::size_of_val(guard),2*std::mem::size_of::<usize>());
   Some(unsafe{[*(guard as *const _ as *const usize),*(guard as *const _ as *const usize).add(1)]})
  },
  Err(error)=>{assert!(matches!(error,ProgramError::AccountBorrowFailed));None},
 };
 drop(actual);
 assert_eq!(unsafe{(*counter).get()},initial);
 let expected=sdk_live_models::MODE(account);
 assert_eq!(unsafe{(*counter).get()},after_actual);
 match expected {
  Ok(guard)=>{
   assert_eq!(std::mem::size_of_val(&guard),2*std::mem::size_of::<usize>());
   let words=unsafe{[*(std::ptr::addr_of!(guard).cast::<usize>()),*(std::ptr::addr_of!(guard).cast::<usize>().add(1))]};
   assert_eq!(observed,Some(words));
   assert_eq!(guard.len(),unsafe{(&*account.data.as_ptr()).len()});
   assert_eq!(guard.as_ptr(),unsafe{(&*account.data.as_ptr()).as_ptr()});
   drop(guard);
  },
  Err(error)=>{assert!(matches!(error,ProgramError::AccountBorrowFailed));assert!(observed.is_none());},
 }
'''.replace('METHOD',method).replace('MODE',mode)
helper='''#[cfg(kani)]
#[kani::requires(counter==std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>())]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| unsafe{(*counter).get()}==old(unsafe{(*counter).get()}))]
fn compare_live(account:&AccountInfo<'_>,counter:*const Cell<isize>){
 let initial=unsafe{(*counter).get()};
COMPARE
 assert_eq!(unsafe{(*counter).get()},initial);
}
'''.replace('COMPARE',compare)
s=s.replace('#[cfg(kani)] mod proofs {',helper+'\n#[cfg(kani)] mod proofs {')
(out/'src/lib.rs').write_text(s)
model=R/'tools/s126-sdk-modular-20261021/sdk-live-models.rs'
(out/'src/sdk_live_models.rs').write_bytes(model.read_bytes())
(out/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-live-model-join"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',mode=mode,method=method,source_sha256=sha(out/'src/lib.rs'),model_sha256=sha(model),base_harness_sha256=sha(base),max_buffer_bytes=limit,qualification=__doc__,domain=f'Storage{limit} bytes/every view length0..{limit}, all bytes/metadata, all signed data/lamport borrow flags, all nonzero usize Rc headers. Original registry SDK, no SDK annotations/patches. Complete live std guard representation and exact status/counter/drop effects checked; both calls have counter-only frame.',remaining='Must pass all properties and tie exact model-source hash/registry versions to enclosing caller. ABI/compiler-specific source-helper equivalence is not general runtime heap or whole-S2 closure.'),indent=2)+'\n')
