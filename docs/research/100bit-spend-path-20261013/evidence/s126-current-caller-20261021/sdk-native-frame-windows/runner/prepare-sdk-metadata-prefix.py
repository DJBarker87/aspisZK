#!/usr/bin/env python3
"""Exact source metadata prefix: all rejection statuses before persistent guards.
This cut contains the actual SDK checkpoint try_data_len. No decoder, scanner,
parser or oracle is executed or assumed. Full parent continuation remains open.
"""
from pathlib import Path
import sys,subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-heap-join.py'),str(O),'length','10485760'],check=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
frozen=subprocess.check_output(['git','-C',str(R),'show',freeze+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
def cut(s,name):
 a=s.index('fn '+name);i=s.index('{',a)+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
helpers='\n'.join(cut(frozen,n) for n in ['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts'])
a=frozen.index('fn stage1(');b=frozen.index('    let mut checkpoint_data',a)
native=frozen[a:b].replace('fn stage1(', 'fn native_metadata_prefix(',1)+'    Ok(())\n}'
prior=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/src/lib.rs'
owned=prior.read_text();a=owned.index('pub fn owned_stage1_body(');b=owned.index(' owned_acquire_checkpoint(sdk,guards,checkpoint.data_slot)?;',a)
model=owned[a:b].replace('pub fn owned_stage1_body(program_id:[u8;32],sdk:&mut OwnedSdk,data:&[u8],guards:&mut LiveGuards)', 'fn owned_metadata_prefix(program_id:[u8;32],sdk:&OwnedSdk,data:&[u8])',1)+' Ok(())\n}'
p=O/'src/lib.rs';s=p.read_text().replace('use super::*;', 'use super::*;\nuse solana_program::entrypoint::ProgramResult;\nuse aspis_r1_cost_probe::{verifier,transport::Variant};\n'+helpers+'\n'+native+'\n'+model,1)
s=s.replace('fn three_account_heap_length_join()', 'fn metadata_prefix_join()')
a=s.index(' let selected:usize=kani::any();');b=s.index(' for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);',a)
s=s[:a]+''' let program=Pubkey::new_from_array(kani::any());
 let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);
 let actual=native_metadata_prefix(&program,&accounts,&instruction[..instruction_len]);
 let expected=owned_metadata_prefix(program.to_bytes(),&model,&instruction[..instruction_len]);
 assert!(matches!((&actual,&expected),
  (Ok(()),Ok(()))|
  (Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))|
  (Err(ProgramError::InvalidArgument),Err(ProgramError::InvalidArgument))|
  (Err(ProgramError::InvalidInstructionData),Err(ProgramError::InvalidInstructionData))|
  (Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))));
 kani::cover!(actual.is_ok(),"all original metadata checks pass");
 kani::cover!(matches!(actual,Err(ProgramError::AccountBorrowFailed)),"exact checkpoint size borrow failure");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidArgument)),"exact duplicate-key rejection");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidInstructionData)),"exact instruction rejection");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidAccountData)),"exact metadata rejection");
'''+s[b:]
s=s.replace('initial_counts[slot]', 'initial_counts[0]')
p.write_text(s)
c=O/'Cargo.toml';text=c.read_text().replace('aspis-s126-sdk-heap-length-join','aspis-s126-sdk-metadata-prefix')
text=text.replace('[profile.release]', 'aspis-r1-cost-probe={path="/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-r1-cost-probe",features=["optimized-terminal","program-build"]}\n[profile.release]');c.write_text(text)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze=freeze,source_sha256=sha(s),native_prefix_sha256=sha(native),native_prefix=native,owned_prefix_sha256=sha(model),owned_prefix=model,helpers={n:sha(cut(frozen,n)) for n in ['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts']},max_buffer_bytes=10485760,qualification=__doc__,remaining='Three-account SDK construction domain. Exact source prefix only; persistent guard/scan/child/writeback continuation and runtime-to-heap embedding must still be composed.'),indent=2)+'\n')
