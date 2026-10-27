#!/usr/bin/env python3
"""Validate retained proof/control receipts; never infer endpoint closure."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;ROOT=E.parent.parent
rows=[json.loads(s) for s in (E/'attempts.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
assert len(rows)<=100
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 d=E/'receipts'/str(r['attempt']);src=d/'source.lean'
 if src.exists():assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256']
 out=(d/'out.log').read_text()
 assert r['wall'] is not None and r['peak_RSS_KiB'] is not None and r['swap']=='0'
 if r['exit']==0:
  assert 'sorryAx' not in out
  for ax in re.findall(r'depends on axioms: \[([^\]]*)\]',out,re.S):
   assert set(x.strip() for x in ax.split(',') if x.strip()) <= allowed
  assert '#print axioms' in src.read_text()
kani=[]
for p in sorted((E/'kani').glob('*/invocation.json')):
 d=p.parent;r=json.loads(p.read_text());out=(d/'out.log').read_text();tm=(d/'time.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' in out and re.search(r'^exit=0$',out,re.M)
 assert '-C opt-level=3' in out and 'kani::stub' not in (E/'control.rs').read_text()
 fields={}
 for k,pat in [('wall',r'Elapsed \(wall clock\) time.*: (.+)'),('peak_RSS_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swap',r'Swaps: (\d+)')]:
  fields[k]=re.search(pat,tm)[1]
 assert fields['swap']=='0'
 kani.append(dict(harness=r['harness'],exit=0,revision=r['revision'],print_axioms='N/A (Kani)',**fields))
assert len(kani)<=6
manifest=E/'focused-manifest.json'
if manifest.exists():
 focus=json.loads(manifest.read_text())
 for pin in focus['proof_sources']:
  assert hashlib.sha256((ROOT/pin['path']).read_bytes()).hexdigest()==pin['sha256']
 if {53297,53298,53299} <= {r['attempt'] for r in rows}:
  audit=(E/'receipts/53297/out.log').read_text()
  assert all("'"+n+"'" in audit for n in focus['theorems'])
  assert all(next(r for r in rows if r['attempt']==a)['exit']==0 for a in [53297,53298,53299])
sources=sorted((ROOT/'docs/research/v8-r0-zk-20261009/lean').glob('PV_L2B_*.lean'))
for p in sources:
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^axiom\s',p.read_text(),re.M),p
 assert 'set_option maxHeartbeats' not in p.read_text()
 assert 'set_option maxRecDepth' not in p.read_text()
changed=subprocess.check_output(['git','diff','c57a344726','--','crates','programs'],cwd=ROOT,text=True)
assert changed==''
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
summary=dict(candidate='c57a344726745387efb38d1571d885c69ce829ee',lean_attempts=len(rows),
 lean_success=sum(r['exit']==0 for r in rows),lean_failures=[r['attempt'] for r in rows if r['exit']!=0],
 kani_runs=len(kani),kani=kani,peak_lean_RSS_KiB=max(int(r['peak_RSS_KiB']) for r in rows),
 swap=0,axioms='Successful compiles: subset of propext, Classical.choice, Quot.sound',
 endpoint_premises_removed=0,target='not yet established')
(E/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
