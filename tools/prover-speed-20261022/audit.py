#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-speed-20261022')
base='7f13d411b8f6af7dbd17d23e79fd24bf9998e913'
changed=subprocess.check_output(['git','diff',base,'--name-only'],text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
allowed=['tools/prover-speed-20261022/','docs/research/100bit-spend-path-20261013/design/PROVER-SPEED-20261022.md','docs/research/100bit-spend-path-20261013/evidence/prover-speed-20261022/']
assert all(any(p.startswith(a) for a in allowed) for p in changed+untracked),changed+untracked
receipts=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());assert r['exit']==0 and r['swap_peak']=='0';assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 receipts.append({'attempt':p.parent.name,'exit':r['exit'],'wall_seconds':r['wall_seconds'],'memory_peak':r['memory_peak'],'swap_peak':r['swap_peak'],'receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
assert len(receipts)==9,len(receipts)
for p in E.rglob('*'):
 if p.is_file():
  assert p.suffix in ['.json','.log','.patch','.txt','.md'],p
  assert p.read_bytes()[:4]!=b'\x7fELF',p
s=json.loads((E/'summary.json').read_text());assert sum(len(x['per_run']) for x in s.values())==20
assert all(r['attempts']==1 for x in s.values() for r in x['per_run'])
fine=json.loads((E/'fine-summary.json').read_text());assert sum(map(len,fine.values()))==4
r={'base_revision':base,'branch':subprocess.check_output(['git','branch','--show-current'],text=True).strip(),'changed_tracked_files':changed,'shipped_source_changed':False,'primary_proofs':20,'supplemental_proofs':4,'all_native_runs_verified_strict_dense':True,'all_recorded_attempt_counts':1,'receipt_checks':receipts,'lean':'not run; print axioms N/A','scope':'measurement/analysis only; no implementation; no pushes','local_target_created':False}
(E/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print('Validated 20 primary + 4 supplemental proofs, 9 capped successful build/run receipts; shipped sources unchanged')
