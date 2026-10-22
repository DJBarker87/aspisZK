#!/usr/bin/env python3
"""Unit-return adapter writing the actual Result into an initialized error slot.
Retains real Ref/Error types; overwriting the required initial error drops no guard.
Candidates until every contract and composed bridge check passes. This avoids
Kani's unsupported Arbitrary generation for foreign returned guard types;
no SDK source change, alternate guard or simplified result carrier is used.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);mode=sys.argv[2];bound=int(sys.argv[3]) if len(sys.argv)>3 else 10485760;assert mode in ['shared','exclusive'] and not O.exists();(O/'src').mkdir(parents=True)
method='try_borrow_data' if mode=='shared' else 'try_borrow_mut_data';guard="std::cell::Ref<'b,&'b mut[u8]>" if mode=='shared' else "std::cell::RefMut<'b,&'a mut[u8]>"
success='before>=0 && before<isize::MAX && now==before+1' if mode=='shared' else 'before==0 && now == -1';failure='before<0 || before==isize::MAX' if mode=='shared' else 'before!=0'
s='''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
type Reply<'b,'a> = Result<GUARD,ProgramError>;
fn counter(account:&AccountInfo<'_>)->*const Cell<isize>{std::rc::Rc::as_ptr(&account.data).cast()}
#[kani::requires(matches!(unsafe{&*out.cast::<Reply<'b,'a>>()},Err(ProgramError::AccountBorrowFailed)))]
#[kani::modifies(out.cast::<[u8;std::mem::size_of::<Reply<'static,'static>>()]>(), counter(account).cast_mut().cast::<isize>())]
#[kani::ensures(|_| {
 let before=old(unsafe{(*counter(account)).get()});let now=unsafe{(*counter(account)).get()};
 match unsafe{&*out.cast::<Reply<'b,'a>>()} {
  Ok(guard)=>SUCCESS && std::mem::size_of_val(guard)==2*std::mem::size_of::<usize>() &&
   unsafe{*(guard as *const _ as *const usize)}==account.data.as_ptr() as usize &&
   unsafe{*(guard as *const _ as *const usize).add(1)}==counter(account) as usize,
  Err(e)=>matches!(e,ProgramError::AccountBorrowFailed) && (FAILURE) && now==before,
 }
})]
fn sdk_out<'b,'a>(account:&'b AccountInfo<'a>,out:*mut u8) {
 unsafe{out.cast::<Reply<'b,'a>>().write(account.METHOD());}
}
fn sdk_bridge<'b,'a>(account:&'b AccountInfo<'a>)->Reply<'b,'a>{
 let mut out=Err(ProgramError::AccountBorrowFailed);sdk_out(account,(&mut out as *mut Reply<'b,'a>).cast());out
}
#[cfg(kani)] mod proofs {
use super::*;
HARNESS
}
'''.replace('GUARD',guard).replace('SUCCESS',success).replace('FAILURE',failure).replace('METHOD',method)
base=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-live-contracts/sources'/('sdk-live-'+mode+'-v1/src/lib.rs');b=base.read_text();a=b.index('#[kani::proof_for_contract(');h=b[a:b.rfind('\n}')]
h=h.replace('#[kani::proof_for_contract(AccountInfo::'+method+')]','#[kani::proof_for_contract(sdk_out)]').replace('fn actual_sdk_live_contract()','fn actual_sdk_out_contract()').replace(' let result=account.'+method+'();'," let mut output:Reply<'_ ,'_>=Err(ProgramError::AccountBorrowFailed);sdk_out(&account,(&mut output as *mut Reply<'_ ,'_>).cast());\n let result=output;")
bridge=h.replace('#[kani::proof_for_contract(sdk_out)]','#[kani::proof]\n#[kani::stub_verified(sdk_out)]').replace('fn actual_sdk_out_contract()','fn actual_sdk_out_bridge()').replace(" let mut output:Reply<'_ ,'_>=Err(ProgramError::AccountBorrowFailed);sdk_out(&account,(&mut output as *mut Reply<'_ ,'_>).cast());\n let result=output;",' let result=sdk_bridge(&account);')
s=s.replace('HARNESS',h+'\n'+bridge).replace('10485760',str(bound));(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-live-out-MODE-BOUND-v7"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('MODE',mode).replace('BOUND',str(bound)))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,view_length_bound=bound,domain=('All view lengths0..'+str(bound)+', arbitrary backing bytes, actual AccountInfo metadata and signed counters/Rc fields. Bounds below10MiB are restricted primitive instances; native accepted-class coverage remains required.'),mode=mode,method=method,original_sdk_source_sha256='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a',expected_time='Cached optimized compilation then one actual SDK unit-output contract or its verified real-guard bridge on the existing10MiB/all signed-counter/all nonzero Rc domain.',remaining='Every actual contract/frame/bridge/safety check and cover must pass. Then complete native caller composition and full heap/runtime/ABI/child/oracle/TX2/S1/S6 binding. Generation is not proof.'),indent=2)+'\n')
