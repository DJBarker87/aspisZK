#!/usr/bin/env python3
"""Read-only allocator-request/control evidence guard; no runtime/adoption claim."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claims-allocator-control-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
b=json.loads((P/'source-kit-binding.json').read_text());freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a';assert b['freeze']==freeze
get=lambda rev,path:subprocess.check_output(['git','show',rev+':'+path],cwd=R)
original=get(freeze,'crates/aspis-r1-cost-probe/src/r1_semantic.rs').decode();span=b['frozen_claims_span'];body=original[span['offset']:span['offset']+span['length']]
assert hashlib.sha256(original.encode()).hexdigest()==b['frozen_whole_source_sha256']
assert hashlib.sha256(body.encode()).hexdigest()==b['frozen_claims_sha256']
candidate=get(b['candidate_revision'],b['candidate_source']);assert hashlib.sha256(candidate).hexdigest()==b['candidate_sha256']
assert candidate==(B/'rust-candidates/s1-claims-safe-storage-20261025/claims.rs').read_bytes()
head='use crate::r1_wire::{self as wire,Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'
orig=head+body+'''\n#[cfg(kani)]
pub(crate) fn run(prefix:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{claims(prefix)}
'''
new=head+candidate.decode()+'\n#[cfg(kani)]\n#[path="allocator_claims_proofs.rs"]\nmod proofs;\n'
proof=(R/'tools/s1-claims-allocator-control-20261025/proofs.rs').read_text()
assert 'kani::assume' not in proof and 'transmute' not in proof
assert proof.count('#[kani::stub(')==8
for required in ['assert!(layout.size()==1392)','assert!(layout.align()==4)',
 'assert!(ALLOCATIONS==0)','assert!(DEALLOCATIONS==0)','assert!(ptr==ALLOCATION)',
 'alloc::alloc::alloc_zeroed(layout)','if ALLOCATION_FAILS{return core::ptr::null_mut();}',
 'let data=*value;drop(value);Ok(data)','let original=observe(crate::original_claims::run(&prefix))',
 'let candidate=observe(claims(&prefix))','assert!(first_calls==second_calls)',
 'assert!(first_frees==second_frees)','assert!(first_frees==1)',
 'assert!(matches!(original,Err(Error::Allocation)))',
 'fn allocation_failure(){paired_case(true)}','fn allocation_success(){paired_case(false)}']:
 assert required in proof,required
assert 'fn reallocation_cut' in proof and 'assert!(false);core::ptr::null_mut()' in proof
for n in range(1,5):
 A=E/f's1-claims-allocator-control-v{n}';i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
 assert r['exit_status']==0 and r['watchdog_stop'] is None and r['swaps']==0
 assert r['verification_launched']==(n%2==0)
 assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
 assert 'uninit-checks' not in r['command'] and '--unwinding-assertions' in r['command']
 assert r['command'][r['command'].index('--harness')+1]=='native_claims::proofs::allocation_'+('failure'if n<3 else 'success')
 assert i['guard']==dict(aggregate_rss_limit_bytes=2*2**30,wall_limit_seconds=180,process_limit=64,one_job=True,local_shared_lock=True)
 for f,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/f)==r[key]
 for p in (A/'source').rglob('*'):
  if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
 D=A/'source/min/src';assert (D/'allocator_original.rs').read_text()==orig
 assert (D/'allocator_claims.rs').read_text()==new
 assert (D/'allocator_claims_proofs.rs').read_text()==proof
 assert (D/'probe_claims_allocator.rs').read_bytes()==(R/'tools/s1-claims-allocator-control-20261025/probe.rs').read_bytes()
 assert (D/'allocator_wire.rs').read_bytes()==(E/'s1-native-claims-v2/source/min/src/wire_claims.rs').read_bytes()
 for rel,h in b['files'].items():assert i['source_files'][rel]==h,rel
 if n%2==0:
  log=(A/'stdout.log').read_text();assert '0 of 1102 failed' in log and 'VERIFICATION:- SUCCESSFUL' in log
  assert ('1 of 4 cover properties satisfied'if n==2 else '3 of 4 cover properties satisfied') in log
F=E/'s1-claims-allocator-preparation-v1';f=json.loads((F/'failure.json').read_text());assert f['status']=='SOURCE_PREPARATION_FAILED' and not f['compiler_launched']
print(f'PASS {len(m["files"])} source/evidence hashes; both common allocator outcomes checked: one1392-byte/align4 request, no reallocation, exact failure/decode/drop control. Actual allocator/runtime/init/adoption and whole S1/S6 OPEN.')
