#!/usr/bin/env python3
"""One real RefMut finish block: exact status/observed byte and write set.
The observed index is a ghost argument unused by the source body. The owned
reply allocation may be freed; no other SDK heap/counter/header is writable.
"""
from pathlib import Path
import sys,subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
frozen=subprocess.check_output(['git','-C',str(R),'show',freeze+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
a=frozen.index('fn stage1(');a=frozen.index('    if checkpoint.len() != checkpoint_data.len()',a);b=frozen.index('\n}\n',a)+2;body=frozen[a:b]
s=r'''#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,msg};
#[cfg_attr(kani,kani::requires(checkpoint_data.len()==1768))]
#[cfg_attr(kani,kani::requires(observed<1768))]
#[cfg_attr(kani,kani::modifies(&mut checkpoint_data[..],&mut checkpoint[..]))]
#[cfg_attr(kani,kani::ensures(move |result:&Result<(),ProgramError>| match result {
 Ok(()) => old(checkpoint.len())==1768 && Some(checkpoint_data[observed])==old(checkpoint.get(observed).copied()),
 Err(ProgramError::InvalidAccountData) => old(checkpoint.len())!=1768 && checkpoint_data[observed]==old(checkpoint_data[observed]),
 _ => false,
}))]
fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,mut checkpoint:Vec<u8>,observed:usize)->Result<(),ProgramError> {
'''+body+r'''
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_finish)] #[kani::unwind(1772)]
 fn finish_byte_and_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let reply:[u8;1769]=kani::any();
  let length:usize=kani::any();kani::assume(length<=1769);
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let result=native_finish(&mut guard,reply[..length].to_vec(),observed);
  kani::cover!(result.is_ok(),"source copy postcondition");
  kani::cover!(matches!(result,Err(ProgramError::InvalidAccountData)),"source length rejection postcondition");
 }
}
'''
(O/'src/lib.rs').write_text(s)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-finish-contract"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze=freeze,source_sha256=sha(s),native_finish_source=body,native_finish_sha256=sha(body),qualification=__doc__,domain='Real SDK RefMut over a1768-byte checkpoint, every byte/metadata/lamport value, arbitrary1769 reply bytes and length0..1769, arbitrary observed index0..1768. Requires actual reached checkpoint size; does not prove whole-source entry or runtime embedding.',remaining='Compile/prove the function contract, inspect assigns/ensures properties, then stub_verified in the complete post-child SDK state check; compose exact source entry/reply interpretation.'),indent=2)+'\n')
