#!/usr/bin/env python3
"""Read-only candidate normal-return comparison audit. No adoption claim."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-safe-claims-trace-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
b=json.loads((P/'source-kit-binding.json').read_text())
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a';assert b['freeze']==freeze
get=lambda rev,path:subprocess.check_output(['git','show',rev+':'+path],cwd=R)
candidate=get(b['candidate_revision'],b['candidate_source']);assert hashlib.sha256(candidate).hexdigest()==b['candidate_sha256']
assert candidate==(B/'rust-candidates/s1-claims-safe-storage-20261025/claims.rs').read_bytes()
original=get(freeze,'crates/aspis-r1-cost-probe/src/r1_semantic.rs').decode()
assert hashlib.sha256(original.encode()).hexdigest()==b['frozen_whole_source_sha256']
span=b['frozen_claims_span'];body=original[span['offset']:span['offset']+span['length']]
assert hashlib.sha256(body.encode()).hexdigest()==b['frozen_claims_sha256']
header='use crate::r1_wire::{self as wire,Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'
original_probe=header+body+'''\n#[cfg(kani)]
pub(crate) fn run(prefix:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{claims(prefix)}
'''
candidate_probe=header+candidate.decode()+'\n#[cfg(kani)]\n#[path="safe_claims_proofs.rs"]\nmod proofs;\n'
maintained=(R/'tools/s1-safe-claims-trace-20261025/proofs.rs').read_text()
old=(R/'tools/s1-native-claims-20261025/proofs.rs').read_text();assert maintained.startswith(old)
a=maintained.index('#[kani::proof]',maintained.index('// Direct paired native-result'))
z=maintained.index('// EXCLUDED negative control:');pos=maintained[a:z].strip()
neg=maintained[maintained.index('#[kani::proof]',z):].strip()
assert neg==pos.replace('fn paired_frozen_safe_claims()', 'fn paired_frozen_safe_claims_negative_last_word()',1).replace('assert!(a[p][i].c1.b==b[p][i].c1.b);','assert!(a[p][i].c1.b.0==(b[p][i].c1.b.0 ^ if p==2&&i==28{1}else{0}));')
for n in range(1,7):
 A=E/f's1-safe-claims-trace-v{n}';i=json.loads((A/'input.json').read_text());r=json.loads((A/'receipt.json').read_text())
 assert r['exit_status']==(1 if n==6 else 0)
 assert r['verification_launched']==(n%2==0)
 assert r['swaps']==0 and r['watchdog_stop'] is None
 assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
 assert 'uninit-checks' not in r['command'] and '--unwinding-assertions' in r['command']
 expected='native_claims::proofs::'+('native_claims_full_trace'if n<3 else 'paired_frozen_safe_claims'+('_negative_last_word'if n>=5 else ''))
 assert r['command'][r['command'].index('--harness')+1]==expected
 assert i['guard']==dict(aggregate_rss_limit_bytes=2*2**30,wall_limit_seconds=180,process_limit=64,one_job=True,local_shared_lock=True)
 for f,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/f)==r[key]
 for p in (A/'source').rglob('*'):
  if p.is_file() and p.name!='run.py':assert sha(p)==i['source_files'][str(p.relative_to(A/'source'))]
 D=A/'source/min/src';assert (D/'safe_claims.rs').read_text()==candidate_probe
 wire=(D/'safe_wire_claims.rs').read_bytes();assert wire==(E/'s1-native-claims-v2/source/min/src/wire_claims.rs').read_bytes()
 assert wire.startswith(get(freeze,'crates/aspis-r1-cost-probe/src/r1_wire.rs'))
 proof=(D/'safe_claims_proofs.rs').read_text();assert 'kani::assume' not in proof and 'transmute' not in proof
 if n<3:assert proof==old
 if n>=3:
  assert (D/'original_claims_pair.rs').read_text()==original_probe
  assert maintained.startswith(proof)
  assert 'let original=crate::original_claims::run(&prefix)' in proof
  assert 'let candidate=claims(&prefix)' in proof and 'assert!(first_calls==second_calls)' in proof
  assert '(Err(a),Err(b))=>{assert!(a==b);}' in proof
  assert '_=>{assert!(false);}' in proof
 if n>=5:assert proof==maintained and i['negative_control']
 # Every source in the final reconstruction has a contemporaneous pre/post pin.
 if n==6:
  for rel,h in b['files'].items():assert i['source_files'][rel]==h,rel
 log=(A/'stdout.log').read_text()
 if n in [2,4]:
  assert f'0 of {839 if n==2 else 985} failed' in log and '3 of 3 cover properties satisfied' in log
  assert 'VERIFICATION:- SUCCESSFUL' in log
 if n==6:
  assert '1 of 1001 failed' in log and 'VERIFICATION:- FAILED' in log
  assert 'Failed Checks: assertion failed: a[p][i].c1.b.0 == (b[p][i].c1.b.0 ^ if p == 2 && i == 28 { 1 } else { 0 })' in log
print(f'PASS {len(m["files"])} source/evidence hashes; direct frozen/candidate full normal-return Result and decoder-count comparison. Allocation-failure/init/effect/SDK/caller/artifact/adoption remain OPEN.')
