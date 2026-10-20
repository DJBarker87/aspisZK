#!/usr/bin/env python3
"""Validate the retained packet; never launch a proof, build, or regression."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=next(p for p in E.parents if (p/'Cargo.toml').exists())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(x) for x in (E/'lean/attempts.jsonl').read_text().splitlines()]
assert [x['attempt'] for x in rows]==list(range(8158,8188))
allowed={'propext','Classical.choice','Quot.sound'}
for x in rows:
 out=(E/'lean'/f"out-{x['attempt']}.log").read_text()
 assert f"exit={x['exit_status']}" in out
 assert hashlib.sha256(json.dumps(x['deps'],sort_keys=True).encode()).hexdigest()==x['deps_fingerprint']
 if x['accepted']:
  assert x['exit_status']==0 and x['swaps']==0 and x['axioms']
  assert 'sorryAx' not in out
  p=R/'docs/research/v8-r0-zk-20261009/lean'/x['module']
  assert sha(p)==x['source_sha256'],x['attempt']
  source=subprocess.check_output(['git','show',x['source_revision']+':'+str(p.relative_to(R))],cwd=R)
  assert hashlib.sha256(source).hexdigest()==x['source_sha256']
  for a in x['axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',a,re.S)
   if m: assert {n.strip() for n in m[1].split(',')}<=allowed
 else: assert sha(R/x['source_snapshot'])==x['source_sha256']
last=rows[-1];assert last['accepted'] and len(last['axioms'])==44
for n in ['mask-step-v1','source-step-v1']:
 receipt=json.loads((E/'kani'/n/'receipt.json').read_text())
 assert receipt['exit_status']==0 and receipt['swaps']==0
 assert receipt['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert '--unwinding-assertions' in receipt['command']
 out=(E/'kani'/n/'stdout.log').read_text()
 assert '0 of ' in out and 'failed' in out and 'VERIFICATION:- SUCCESSFUL' in out
 pins=json.loads((E/'kani'/(n+'-inputs.json')).read_text())
 for p,s in pins['source_hashes'].items():assert sha(R/p)==s
subprocess.run(['python3',str(E/'harness/check-step-source.py')],cwd=R,check=True,stdout=subprocess.DEVNULL)
check=json.loads((E/'checklist-before-after.json').read_text())
p=R/'docs/research/v8-r0-zk-20261009/r1p-final/PRIVACY-FINAL-20261020.md'
assert sha(p)==check['checklist_sha256']
assert len(check['rows'])==9
report=(R/'docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT5-20261021.md').read_text()
for row in check['rows']:
 assert row['before_verbatim']==row['after_verbatim'] and not row['discharged']
 assert report.count(row['before_verbatim'])==2
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
for p in elf['programs'].values():
 assert p['byte_identical'] and p['cmp_exit']==0 and p['sha256']==p['expected_sha256']
 assert p['receipt']['exit_status']==0 and p['receipt']['swaps']==0
for p,s in json.loads((E/'elf-source-inventory.json').read_text())['files'].items():assert sha(R/p)==s
for p,s in json.loads((E/'source-release.json').read_text())['files'].items():assert sha(R/p)==s
assert all(p.suffix not in ['.olean','.so','.llbc','.tar','.gz'] for p in E.rglob('*') if p.is_file())
assert not (R/'target').exists()
print('Validated 30 focused attempts, 44 final axiom audits, 2 single-step Kani proofs, 3 frozen ELFs, and 9 unchanged source rows.')
