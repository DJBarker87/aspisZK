#!/usr/bin/env python3
"""Isolate the exact frozen stage1 length/prefix/tag guard, all rejection paths.
No production changes. Native SDK Ref and full ProgramError remain concrete.
The scalar reference is a proof candidate until native equality, totality and
complete parent fission/composition gates are checked.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
rev='b2727acd3abf79315d18b754a260f58f4b1c6326';path='programs/r1-cost-probe/src/r1_pool_adapter.rs'
frozen=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path],text=True)
a=frozen.index('    let proof_length = verifier::PROOF_BYTES;',frozen.index('fn stage1('));b=frozen.index('    let checkpoint = super::first_decoded',a);guard=frozen[a:b]
s='''#![allow(dead_code,unexpected_cfgs)]
use solana_program::program_error::ProgramError;
use aspis_r1_cost_probe::{verifier,transport::Variant};
use aspis_statement::pool_v1::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;

pub fn native_gate(proof_data:&std::cell::Ref<'_,&mut [u8]>,candidate:[u8;688])->Result<(usize,usize),ProgramError> {
'''+guard+'''    Ok((proof_start,proof_end))
}

pub fn prefix_different(bytes:&[u8],candidate:&[u8])->bool {
 if bytes.len()<candidate.len() {return true;}
 let mut offset=0;
 while offset<candidate.len() {
  if bytes[offset]!=candidate[offset] {return true;}
  offset+=1;
 }
 false
}

pub fn reference_gate(proof_data:&[u8],candidate:&[u8;688])->Result<(usize,usize),ProgramError> {
 let proof_length=57607usize;
 let proof_start=688usize;
 let proof_end=proof_start.checked_add(proof_length).ok_or(ProgramError::InvalidAccountData)?;
 if proof_data.len()!=proof_end {return Err(ProgramError::InvalidAccountData);}
 if prefix_different(proof_data,candidate) {return Err(ProgramError::InvalidAccountData);}
 if proof_data[proof_start+8]!=2 {return Err(ProgramError::InvalidAccountData);}
 Ok((proof_start,proof_end))
}

#[cfg(kani)] mod proofs {
 use super::*;
 use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
 #[kani::proof] #[kani::unwind(700)]
 fn actual_sdk_guard_reference() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;58296]=kani::any();let candidate:[u8;688]=kani::any();
  let length:usize=kani::any();kani::assume(length<=58296);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes[..length],&owner,flags[2],rent);
  let data=account.try_borrow_data().unwrap();
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<std::cell::Cell<isize>>();
  let before=unsafe{(*counter).get()};let pointer=data.as_ptr();
  let actual=native_gate(&data,candidate);
  let expected=reference_gate(&data,&candidate);
  assert_eq!(actual,expected);
  assert_eq!(data.as_ptr(),pointer);assert_eq!(data.len(),length);
  assert_eq!(unsafe{(*counter).get()},before);
  kani::cover!(actual.is_ok(),"guard accepts equal candidate and tag2");
  kani::cover!(length!=58295,"guard rejects length");
  kani::cover!(length==58295&&data[0]!=candidate[0],"guard rejects prefix mismatch");
  kani::cover!(length==58295&&data[696]!=2,"guard rejects tag mismatch");
 }
}
'''
if len(sys.argv)>2 and sys.argv[2]=='frame':
 s=s.replace('pub fn native_gate(', '#[cfg_attr(kani,kani::modifies())]\npub fn native_gate(',1)
 s=s.replace('#[kani::proof] #[kani::unwind(700)]', '#[kani::proof_for_contract(native_gate)] #[kani::unwind(700)]')
if len(sys.argv)>2 and sys.argv[2]=='other-lengths':
 a=s.index(' #[kani::proof] #[kani::unwind(700)]');b=s.index('\n}\n',a)
 s=s[:a]+''' #[kani::proof] #[kani::unwind(8)]
 fn actual_sdk_guard_other_lengths() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;10485760]=kani::any();let candidate:[u8;688]=kani::any();
  let length:usize=kani::any();kani::assume(length<=10485760);kani::assume(length!=58295);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes[..length],&owner,flags[2],rent);
  let data=account.try_borrow_data().unwrap();
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<std::cell::Cell<isize>>();
  let before=unsafe{(*counter).get()};let pointer=data.as_ptr();
  let actual=native_gate(&data,candidate);
  assert_eq!(actual,Err(ProgramError::InvalidAccountData));
  assert_eq!(data.as_ptr(),pointer);assert_eq!(data.len(),length);
  assert_eq!(unsafe{(*counter).get()},before);
  kani::cover!(length==10485760,"maximum runtime buffer rejects without scanning");
  kani::cover!(length==0,"empty runtime buffer rejects without scanning");
 }'''+s[b:]
(O/'src/lib.rs').write_text(s)
host='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src'
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-proof-gate"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-statement={path="ROOT/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
aspis-r1-cost-probe={path="ROOT/crates/aspis-r1-cost-probe",features=["optimized-terminal","program-build"]}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('ROOT',host))
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=rev,path=path,source_sha256=sha(s),frozen_guard=guard,frozen_guard_sha256=sha(guard),qualification=__doc__,domain='Actual AccountInfo/Ref guard over all58296 storage-byte arrays, every slice length0..58296, arbitrary688-byte candidate and complete SDK metadata. Exact full ProgramError equality includes length/prefix/tag errors. No seeded prefix or tag, no scan/decoder/verifier hook. Higher lengths, arbitrary runtime heap/borrow construction, complete parent fission and ordered caller composition remain explicit.'),indent=2)+'\n')

if len(sys.argv)>2 and sys.argv[2]=='other-lengths':
 p=O/'source-cut.json';meta=json.loads(p.read_text());meta['domain']='Actual AccountInfo/Ref over all10485760-byte storage arrays, arbitrary candidate/metadata and every slice length0..10485760 except58295. The complete unchanged native guard must reject InvalidAccountData without prefix/tag traversal; exact pointer/length/counter observations retained. Together with the separate matching-length/prefix/tag certificate this covers the runtime10MiB length domain, subject to the still-explicit runtime heap/parent composition gate.';p.write_text(json.dumps(meta,indent=2)+'\n')

if len(sys.argv)>2 and sys.argv[2]=='frame':
 p=O/'source-cut.json';meta=json.loads(p.read_text());meta['frame']='Empty modifies set on the exact native SDK Ref guard; proof_for_contract must verify no caller memory write. The same full return equality and pointer/length/counter checks remain. No unproved contract stub is used.';p.write_text(json.dumps(meta,indent=2)+'\n')
