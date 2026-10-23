#!/usr/bin/env python3
"""Derive reference-prefix admission facts from actual native decoder entry.
No owned reference or SDK model stubs execute. These facts plus independently
checked byte frames/actual scan transport can construct the emitted reference
prefix, avoiding a second full SDK execution in the same solver target.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-prefix-frame.py'),str(out)],check=True)
p=out/'src/lib.rs';s=p.read_text();s=s.replace('#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]','#[kani::proof] #[kani::unwind(48)]')
a=s.index('#[kani::modifies(');b=s.index('fn native_prefix(',a);s=s[:a]+s[b:]
needle=' assert_eq!(amounts,initial_amounts);';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 if unsafe{HITS.value[0]}==1 {
  assert_eq!(account_count,3,"native decoder entry derives account arity");
  assert_eq!(instruction_len,2,"native decoder entry derives instruction length");
  assert_eq!(instruction[0],3,"native decoder entry derives stage selector");
  assert!(instruction[1]==10 || instruction[1]==11,"native decoder entry derives split domain");
  assert!(keys[0]!=keys[1] && keys[0]!=keys[2] && keys[1]!=keys[2],"native decoder entry derives distinct account keys");
  assert!(!flags[0][0] && !flags[0][1] && !flags[0][2],"native decoder entry derives readonly proof metadata");
  assert!(!flags[1][0] && !flags[1][1] && !flags[1][2],"native decoder entry derives readonly public metadata");
  assert!(owners[2]==program && !flags[2][0] && flags[2][1] && !flags[2][2],"native decoder entry derives checkpoint ownership and flags");
  assert_eq!(data_slots[1],1,"native decoder entry identifies original public allocation");
  assert_eq!(data_slots[2],2,"native decoder entry identifies original checkpoint allocation");
  assert_eq!(initial_counts[2],0,"native decoder entry derives checkpoint exclusive-borrow admission");
  assert!(initial_counts[1]>=0 && initial_counts[1]<isize::MAX,"native decoder entry derives public shared-borrow admission");
  assert!(matches!(&actual,Err(ProgramError::InvalidAccountData)),"native decoder-error cut returns the exact error");
 }
''')
p.write_text(s)
p=out/'Cargo.toml';p.write_text(p.read_text().replace('name="aspis-s126-sdk-shared-prefix"','name="aspis-s126-sdk-shared-prefix-entry-facts"'))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All properties and covers must pass. Actual std scan=false/all-zero transport and initial-byte preservation are independent checked boundaries, not assumed here. Need explicit reference-prefix construction and source/cut transport, then successful child/guard/gate/writeback/runtime/oracle composition. No full stage1 or S2 closure.')
p.write_text(json.dumps(m,indent=2)+'\n')
