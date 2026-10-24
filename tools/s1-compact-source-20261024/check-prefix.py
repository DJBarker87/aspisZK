#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
subprocess.run([sys.executable,str(Path(__file__).with_name('check.py'))],check=True)
m=json.loads((E/'s1-native-compact-prefix-targets.json').read_text());rs={}
for n,rel in m['targets'].items():
 r=json.loads((E/rel).read_text());rs[n]=r
 assert r['exit_status']==0 and r['swaps']==0 and r['target']==n,n
 assert hashlib.sha256((S/(n+'.lean')).read_bytes()).hexdigest()==r['source_sha256'],n
 for report in r['print_axioms']:
  assert 'sorryAx' not in report
  names=re.search(r'axioms: \[(.*?)\]',report,re.S)
  if names:assert set(names[1].replace(' ','').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(n+'.lean')).read_text())
for n,r in rs.items():
 for dep,owner in r['direct_imports'].items():
  if dep in rs:assert owner['sha256']==rs[dep]['object_sha256'],(n,dep)
for rel,h in m['files'].items():assert hashlib.sha256((R/rel).read_bytes()).hexdigest()==h,rel
print(json.dumps({'native_prefix_targets':len(rs),'wall_seconds':sum(r['wall_seconds'] for r in rs.values()),'swaps':0,'status':'accepted-only native expansion prefix; actual prepare/parser join open'}))
