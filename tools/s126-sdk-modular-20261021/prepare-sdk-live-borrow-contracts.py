#!/usr/bin/env python3
"""Annotate an isolated SDK copy, retaining exact original method bodies.
Contracts are candidates until their actual-method harnesses pass. No production
SDK/source is edited; stripping inserted cfg(kani) annotations restores all
original SDK source bytes. The live-guard representation is checked explicitly.
"""
from pathlib import Path
import hashlib,json,sys
registry,sdk,harness=map(Path,sys.argv[1:4])
mode=sys.argv[4] if len(sys.argv)>4 else 'length'
assert mode in ['length','shared','exclusive']
sdk.mkdir(parents=True,exist_ok=False);harness.mkdir(parents=True,exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
original=(registry/'src/lib.rs').read_text()
assert sha(original.encode())=='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a'
for name in ['Cargo.toml','Cargo.toml.orig','src/lib.rs','src/debug_account_data.rs']:
 p=sdk/name;p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes((registry/name).read_bytes())
counter='unsafe{(*Rc::as_ptr(&self.data).cast::<std::cell::Cell<isize>>()).get()}'
method={'length':'try_data_len','shared':'try_borrow_data','exclusive':'try_borrow_mut_data'}[mode]
if mode=='length':
 post='''match result {
            Ok(n)=>before>=0 && before<isize::MAX && *n==unsafe{(&*self.data.as_ptr()).len()} && now==before,
            Err(e)=>matches!(e,ProgramError::AccountBorrowFailed) && (before<0 || before==isize::MAX) && now==before,
        }'''
else:
 success='before>=0 && before<isize::MAX && now==before+1' if mode=='shared' else 'before==0 && now == -1'
 failure='before<0 || before==isize::MAX' if mode=='shared' else 'before!=0'
 post='''match result {
            Ok(guard)=>SUCCESS && std::mem::size_of_val(guard)==2*std::mem::size_of::<usize>() &&
                unsafe{*(guard as *const _ as *const usize)}==self.data.as_ptr() as usize &&
                unsafe{*(guard as *const _ as *const usize).add(1)}==Rc::as_ptr(&self.data) as usize,
            Err(e)=>matches!(e,ProgramError::AccountBorrowFailed) && (FAILURE) && now==before,
        }'''.replace('SUCCESS',success).replace('FAILURE',failure)
annotation='''    #[cfg_attr(kani,kani::modifies(Rc::as_ptr(&self.data).cast_mut().cast::<isize>()))]
    #[cfg_attr(kani,kani::ensures(|result| {
        let before=old(COUNTER);let now=COUNTER;
        POST
    }))]
'''.replace('COUNTER',counter).replace('POST',post)
needle='    pub fn '+method+'('
assert original.count(needle)==1
annotated=original.replace(needle,annotation+needle)
assert annotated.replace(annotation,'')==original
(sdk/'src/lib.rs').write_text(annotated)
remote_sdk='/home/dombarker/project-offloads/s126-real-sdk-20261021/'+sdk.name
(harness/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-live-borrow-contract"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[patch.crates-io]
solana-account-info={path="REMOTE"}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('REMOTE',remote_sdk))
source=r'''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof_for_contract(AccountInfo::METHOD)] #[kani::unwind(36)]
fn actual_sdk_live_contract(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
 let mut bytes:[u8;10485760]=kani::any();let length:usize=kani::any();kani::assume(length<=10485760);
 let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes[..length],&owner,flags[2],rent_epoch);
 let data=std::rc::Rc::as_ptr(&account.data);let amount=std::rc::Rc::as_ptr(&account.lamports);
 let counter=data.cast::<Cell<isize>>();let amount_counter=amount.cast::<Cell<isize>>();
 let fields=[unsafe{data.cast::<usize>().sub(2).cast_mut()},unsafe{data.cast::<usize>().sub(1).cast_mut()},unsafe{amount.cast::<usize>().sub(2).cast_mut()},unsafe{amount.cast::<usize>().sub(1).cast_mut()}];
 for field in fields {assert_eq!(unsafe{*field},1);}
 let rc:[usize;4]=kani::any();for count in rc {kani::assume(count>=1);}
 for i in 0..4 {unsafe{*fields[i]=rc[i];}}
 assert_eq!(std::rc::Rc::strong_count(&account.data),rc[0]);assert_eq!(std::rc::Rc::weak_count(&account.data),rc[1]-1);
 assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc[2]);assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc[3]-1);
 let initial:isize=kani::any();let initial_amount:isize=kani::any();
 unsafe{(*counter).set(initial);(*amount_counter).set(initial_amount);}
 let result=account.METHOD();
 drop(result);
 assert_eq!(unsafe{(*counter).get()},initial);assert_eq!(unsafe{(*amount_counter).get()},initial_amount);
 for i in 0..4 {assert_eq!(unsafe{*fields[i]},rc[i]);}
 unsafe{(*counter).set(0);(*amount_counter).set(0);}
 for field in fields {unsafe{*field=1;}}
 kani::cover!(initial==0&&length==10485760,"maximum view ordinary source contract");
 kani::cover!(initial==isize::MAX&&length==0,"saturated counter empty source contract");
 kani::cover!(initial == -1 && rc[0]==usize::MAX,"exclusive counter and full Rc domain");
}
}
'''.replace('METHOD',method)
(harness/'src').mkdir();(harness/'src/lib.rs').write_text(source)
meta=dict(schema='focused-extractor-proof-packet-v1',mode=mode,method=method,original_sdk_source_sha256=sha(original.encode()),annotated_sdk_source_sha256=sha(annotated.encode()),annotation=annotation,strip_annotations_restores_exact_original=True,harness_source_sha256=sha(source.encode()),domain='One actual typed SDK AccountInfo, storage10MiB and every view length0..10MiB, all byte values and metadata, every signed data/lamport borrow flag, every nonzero usize Rc header. Checked body is the unchanged SDK method; returned guard is dropped by the harness only after checking the method postcondition.',qualification=__doc__,remaining='Annotations and successful codegen alone prove nothing. Need every method contract property checked before use in actual native caller; source/heap embedding, error/log/oracle and child installation remain separate.')
for folder in [sdk,harness]:(folder/'source-cut.json').write_text(json.dumps(meta,indent=2)+'\n')
