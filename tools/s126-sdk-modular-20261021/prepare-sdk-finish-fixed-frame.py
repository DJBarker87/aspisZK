#!/usr/bin/env python3
"""Exact frozen RefMut finish block, successful fixed-size reply domain.
Ghost fixed-array pointers make the write-set size constant; the actual Vec reply is borrowed and a ghost byte is required equal to its pre-call byte; no SDK carrier
or source-body replacement. Failed length replies remain a separate cut.
"""
from pathlib import Path
import sys,subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
raw=subprocess.check_output(['git','-C',str(R),'show',freeze+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
a=raw.index('fn stage1(');a=raw.index('    if checkpoint.len() != checkpoint_data.len()',a);b=raw.index('\n}\n',a)+2;body=raw[a:b]
s=r'''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,msg};
#[cfg_attr(kani,kani::requires(checkpoint_data.len()==1768 && checkpoint.len()==1768))]
#[cfg_attr(kani,kani::requires(observed<1768))]
#[cfg_attr(kani,kani::requires(destination==checkpoint_data.as_mut_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::requires(source==checkpoint.as_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::requires(expected==checkpoint[observed]))]
#[cfg_attr(kani,kani::modifies(destination))]
#[cfg_attr(kani,kani::ensures(|result:&Result<(),ProgramError>| result.is_ok() && checkpoint_data[observed]==expected))]
fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,checkpoint:&Vec<u8>,observed:usize,destination:*mut [u8;1768],source:*const [u8;1768],expected:u8)->Result<(),ProgramError> {
'''+body+r'''
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_finish)] #[kani::unwind(1772)]
 fn exact_finish_fixed_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let reply:[u8;1768]=kani::any();let checkpoint=reply.to_vec();
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let destination=guard.as_mut_ptr().cast::<[u8;1768]>();let source=checkpoint.as_ptr().cast::<[u8;1768]>();
  let expected=checkpoint[observed];
  let result=native_finish(&mut guard,&checkpoint,observed,destination,source,expected);
  kani::cover!(result.is_ok()&&observed==0,"fixed-size native whole copy first byte");
  kani::cover!(result.is_ok()&&observed==1767,"fixed-size native whole copy last byte");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-finish-fixed-frame"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze=freeze,source_sha256=hashlib.sha256(s.encode()).hexdigest(),native_finish_source=body,native_finish_sha256=hashlib.sha256(body.encode()).hexdigest(),qualification=__doc__,domain='Actual RefMut and full ProgramError; checkpoint/source both1768 bytes, every byte, ghost observed index0..1768, metadata/lamports arbitrary. Modifies only the fixed1768-byte destination array; the actual Vec reply is borrowed and its owner/drop remains outside the helper. Does not establish rejected-length or parent source joins.',remaining='Contract compile/proof/property audit; install verified callee in full SDK post-child state, derive fixed-size/reached-state/child-return premises from source caller and R22, then compose whole enclosing source/log join.'),indent=2)+'\n')
