#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=Path(__file__).resolve().parent
for name in ['semantic.py','prepared.py','caller.py']:subprocess.run([sys.executable,str(P/name),'--check'],check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((E/'s1-prepare-count-targets.json').read_text());pins=json.loads((E/'s1-prepare-count-import-pins.json').read_text())
for n,a in m['targets'].items():
 p=S/(n+'.lean');r=json.loads((E/a/'receipt.json').read_text())
 assert r['target']==n and r['exit_status']==0 and r['source_sha256']==sha(p),n
 assert sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][n]['source_sha256'],n
 assert r['object_sha256']==pins['targets'][n]['object_sha256'],n
 assert '-j1' in r['command'] and '-M4400' in r['command'] and r['swaps']==0,n
 assert r['peak_rss_bytes']<4400*1024**2 and r['print_axioms'],n
 for s in r['print_axioms']:
  if 'does not depend on any axioms' in s:continue
  found=re.search(r'depends on axioms:\s*\[([^]]*)\]',s,re.S);assert found
  assert set(re.findall(r'[A-Za-z_.]+',found[1]))<={'propext','Classical.choice','Quot.sound'},(n,s)
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),n
for path,h in json.loads((E/'s1-prepare-count-tool-pins.json').read_text())['scripts'].items():assert sha(R/path)==h,path
# Each direct dependency compiled in this packet must match its final selected object.
for n,a in m['targets'].items():
 r=json.loads((E/a/'receipt.json').read_text())
 for dep,info in r['direct_imports'].items():
  if dep in m['targets']:assert info['sha256']==pins['targets'][dep]['object_sha256'],(n,dep)
print(json.dumps({'targets':len(m['targets']),'metrics':m['metrics'],'release_none_prepare_model_bound':115,'whole_driver_or_frozen_sdk_closure':False}))
