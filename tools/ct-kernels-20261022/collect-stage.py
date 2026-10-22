#!/usr/bin/env python3
"""Collect only text receipts, hashes and measurements; never binaries/keys."""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];stage=sys.argv[1];name=sys.argv[2]
assert stage.replace('-','').isalnum() and name.replace('-','').isalnum()
E=R/'docs/research/100bit-spend-path-20261013/evidence'/name;E.mkdir(exist_ok=True)
remote='dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-ct-kernels-v2-20261022/src/'
subprocess.run(['rsync','-az','--include=/'+stage+'-*/***','--include=/elf-'+('v2final' if stage=='v2' else stage)+'-*/***','--exclude=*',remote+'receipts/',str(E/'receipts')+'/'],check=True)
subprocess.run(['rsync','-az','--include=/reservation-'+stage+'-*.json','--include=/reservation-elf-'+('v2final' if stage=='v2' else stage)+'-*.json','--exclude=*',remote,str(E)+'/'],check=True)
for src,dst in [('elf-identities.json','elf-identities.json'),(stage+'-fixture-identities.json','fixture-identities.json')]:
 subprocess.run(['rsync','-az',remote+src,str(E/dst)],check=True)
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());assert r['swaps']==0 and r['cgroup_swap_peak_bytes']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 rows.append({k:r[k] for k in ['attempt','target','source_revision','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps','print_axioms']})
assert len(rows)>=5,rows
assert all(r['byte_equal'] and r['expected_sha256']==r['sha256'] for r in json.loads((E/'elf-identities.json').read_text()))
assert json.loads((E/'fixture-identities.json').read_text())['proof_and_public_byte_identity']
(E/'summary.json').write_text(json.dumps(dict(stage=stage,status='passes at documented per-step and source L2 boundary',attempts=rows),indent=2)+'\n')
(E/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(E))+'\n' for p in sorted(E.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
print(json.dumps(dict(stage=stage,attempts=len(rows),evidence=str(E))))
