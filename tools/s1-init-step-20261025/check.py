#!/usr/bin/env python3
"""Read-only scope/hash check. No compiler replay and no adoption claim."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
P=E/'s1-init-step-20261025'
C=B/'rust-candidates/s1-claims-safe-storage-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():assert sha(R/rel)==h,rel
b=json.loads((C/'source-binding.json').read_text())
old=subprocess.check_output(['git','show',b['freeze']+':'+b['path']],cwd=R,text=True)
new=(C/'r1_semantic.rs').read_text();body=(C/'claims.rs').read_text()
a=old.index('#[inline(never)]\nfn claims(');z=old.index('\n#[inline(never)]',a+1)
assert new==old[:a]+body+old[z:]
assert hashlib.sha256(old.encode()).hexdigest()==b['frozen_sha256']
assert sha(C/'r1_semantic.rs')==b['candidate_sha256']
assert sha(C/'claims.rs')==b['candidate_function_sha256']
assert 'unsafe' not in body
assert 'Result<Box<[[QM31; 29]; 3]>, Error>' in body
assert 'let record = prefix.validated_record(25)?;' in body
assert 'out[p] = record.decode_k::<29>(p * 29)?;' in body
assert 'for p in 0..3' in body
for name in ['s1-init-step-v1','s1-init-step-v2','s1-claims-safe-typecheck-v1']:
    a=E/name;r=json.loads((a/'receipt.json').read_text());i=json.loads((a/'input.json').read_text())
    for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(a/file)==r[key]
    assert all(r['source_unchanged'].values()) and all(r['tools_unchanged'].values())
    assert r['swaps']==0 and r['watchdog_stop'] is None
    for f in (a/'source').rglob('*'):
        if f.is_file() and f.suffix!='.py':assert sha(f)==i['source_files'][str(f.relative_to(a/'source'))]
    if name.endswith('typecheck-v1'):
        assert r['exit_status']==0 and not r['verification_launched']
        probe=(a/'source/min/src/candidate_claims.rs').read_text()
        assert probe.endswith(body)
    elif name.endswith('v2'):
        s=(a/'stdout.log').read_text()
        assert r['exit_status']!=0 and 'Interaction between raw pointers and unions' in s
        assert 'Option<r1_wire::Error>' in s
print(f"PASS {len(m['files'])} source/evidence hashes; one-function candidate only; native initializedness/equivalence/adoption OPEN")
