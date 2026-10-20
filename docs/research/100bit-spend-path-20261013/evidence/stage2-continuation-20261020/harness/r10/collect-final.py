#!/usr/bin/env python3
"""Collect final-source receipts, check exact regressions and pin retained ELFs."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020');O=H/'publication-r10';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for d in sorted((H/'receipts').glob('r10-*')):
 r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0,(d,r)
 t=O/'receipts'/d.name;t.mkdir(parents=True,exist_ok=True)
 for n in ['receipt.json','time.log','stderr.log']:shutil.copy2(d/n,t/n)
 p=d/'stdout.log';(t/'stdout-pin.json').write_text(json.dumps(dict(sha256=sha(p),bytes=p.stat().st_size),indent=2)+'\n')
 if p.stat().st_size<200000:shutil.copy2(p,t/p.name)
 rows.append(dict(run=d.name,**r))
for name in ['counter-adopted','counter-audit-eight-way']:
 p=H/'runs-r10'/(name+'.json');base=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/runs')/(name+'.json')
 a=json.loads(p.read_text());b=json.loads(base.read_text())
 for r in [a,b]:r['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x:x['input_hex'])
 assert all(a[k]==b[k] for k in ['ordered_digest_calls','hash_input_counts','acceptance'])
 (O/(name+'-comparison.json')).write_text(json.dumps(dict(actual_sha256=sha(p),baseline_sha256=sha(base),calls=len(a['ordered_digest_calls']),ordered_calls_counts_acceptance_equal=True),indent=2)+'\n')
p=H/'receipts/r10-gate-codec-1233/stdout.log';assert sha(p)=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321'
(O/'codec.json').write_text(json.dumps(dict(outputs=1233,sha256=sha(p),baseline_byte_identical=True),indent=2)+'\n')
for source,dest in [(H/'cu-r10.json','cu.json'),(H/'runs-r10/r1p-retry-gate.json','r1p-retry-gate.json'),(H/'stack-r10/verifier/stack-audit.json','stack-audit.json')]:shutil.copy2(source,O/dest)
artifacts=[]
for n in ['aspis_r1_cost_probe_program.so','linked.elf']:
 p=H/'artifacts/verifier'/n;artifacts.append(dict(name=n,sha256=sha(p),bytes=p.stat().st_size,retained_host_path=str(p)))
(O/'artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
(O/'runs.json').write_text(json.dumps(rows,indent=2)+'\n');print('collected',len(rows),'successful final-source receipts')
