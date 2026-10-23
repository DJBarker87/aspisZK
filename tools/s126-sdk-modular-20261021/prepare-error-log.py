#!/usr/bin/env python3
"""Exact frozen adapter error/log leaf versus owned static-string reference."""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
rev='b2727acd3abf79315d18b754a260f58f4b1c6326';path='programs/r1-cost-probe/src/lib.rs'
frozen=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path],text=True)
a=frozen.index('fn error(');i=frozen.index('{',a)+1;depth=1
while depth:depth+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
body=frozen[a:i]
s='''#![allow(dead_code,unexpected_cfgs)]
use aspis_r1_cost_probe::verifier;
use solana_program::{msg,program_error::ProgramError};
'''+body+'''
fn owned_error(error:verifier::Error)->ProgramError {
 let message=match error {
'''
errors=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']
for name in errors:s+='  verifier::Error::'+name+'=>"r1:error:'+name+'",\n'
s+=''' };
 solana_program::log::sol_log(message);
 ProgramError::InvalidInstructionData
}
#[cfg(kani)] mod proofs {
 use super::*;
 static mut LOG:Option<Vec<u8>>=None;
 static mut CALLS:u8=0;
 fn capture(message:&str) {unsafe{assert!(LOG.is_none());LOG=Some(message.as_bytes().to_vec());CALLS+=1;}}
 #[kani::proof]
 #[kani::unwind(32)]
 #[kani::stub(solana_program::log::sol_log,capture)]
 fn actual_error_log_owned_correspondence() {
  let tag:u8=kani::any();kani::assume(tag<8);
  let error=match tag {
'''
for n,name in enumerate(errors):s+='   '+str(n)+'=>verifier::Error::'+name+',\n'
s+='''   _=>unreachable!(),
  };
  let reference=match tag {
'''
for n,name in enumerate(errors):s+='   '+str(n)+'=>verifier::Error::'+name+',\n'
s+='''   _=>unreachable!(),
  };
  unsafe{LOG=None;CALLS=0;}
  let actual=super::error(error);
  let actual_log=unsafe{LOG.take().unwrap()};assert_eq!(unsafe{CALLS},1);
  unsafe{CALLS=0;}
  let expected=owned_error(reference);
  let expected_log=unsafe{LOG.take().unwrap()};
  assert_eq!(unsafe{CALLS},1);
  assert!(matches!(actual,ProgramError::InvalidInstructionData));
  assert!(matches!(expected,ProgramError::InvalidInstructionData));
  assert_eq!(actual_log,expected_log);
  kani::cover!(tag==0,"Parse log");kani::cover!(tag==7,"Allocation log");
 }
}
'''
mode=sys.argv[2] if len(sys.argv)>2 else 'symbolic'
if mode=='parse':
 s=s.replace('let tag:u8=kani::any();kani::assume(tag<8);','let tag:u8=0;')
 s=s.replace('kani::cover!(tag==0,"Parse log");kani::cover!(tag==7,"Allocation log");','kani::cover!(tag==0,"Parse log");')
 s=s.replace('actual_error_log_owned_correspondence','actual_error_parse_owned_correspondence')
(O/'src/lib.rs').write_text(s)
host='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src'
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-error-log-CASE"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-r1-cost-probe={path="ROOT/crates/aspis-r1-cost-probe",features=["optimized-terminal","program-build"]}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('ROOT',host).replace('CASE',mode))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=rev,path=path,original_error=body,original_error_sha256=hashlib.sha256(body.encode()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,boundary='Only solana_program::log::sol_log is replaced by a capturing observer. Both actual Debug formatter and owned reference use this same logging boundary; checks exact UTF8 bytes, one log call, and complete returned error variant. No SDK-log-runtime implementation claim.'),indent=2)+'\n')
