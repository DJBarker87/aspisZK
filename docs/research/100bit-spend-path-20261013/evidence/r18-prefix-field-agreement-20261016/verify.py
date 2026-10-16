#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
b=Path(__file__).resolve().parent;root=b.parents[4];base=root/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
counts={'field-agreement-a':0,'discriminant-original-a':1,'types-bridge-a':0,'funs-bridge-a':0,'discriminant-bridge-a':1,'step-bridge-a':1,'trace-bridge-a':4,'parse-bridge-a':3,'field-agreement-bridge-a':5}
for a,count in counts.items():
 d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text());log=(d/'lean.log').read_text()
 assert r['exit_status']==(1 if a=='field-agreement-a' else 0),a
 assert r['source_sha256']==sha(d/'source.lean'),a
 assert r['runner_sha256']==sha(d/'runner.py'),a
 assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json')),a
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['memory_events_before']==r['memory_events_after']
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
 if a=='field-agreement-a':
  assert 'instDiscriminantErrorIsize' in log and 'environment already contains' in log
 else:
  reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
  noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",log)
  assert len(reports)+len(noaxioms)==count,(a,reports,noaxioms)
  for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
  assert 'sorryAx' not in log and 'error:' not in log,a
for module,attempt in [('ExtractedPrefixFieldAgreement','field-agreement-bridge-a'),('ExtractedPrefixRecordStep','step-bridge-a'),('ExtractedPrefixTrace','trace-bridge-a'),('ExtractedPrefixParse','parse-bridge-a')]:
 assert (base/'lean'/f'{module}.lean').read_bytes()==(b/'runs'/attempt/'source.lean').read_bytes()
assert (base/'lean/bridge-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Types.lean').read_bytes()==(b/'runs/types-bridge-a/source.lean').read_bytes()
assert (base/'lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean').read_bytes()==(b/'runs/funs-bridge-a/source.lean').read_bytes()
assert (b/'runs/discriminant-original-a/lean.log').read_bytes()==(b/'runs/discriminant-bridge-a/lean.log').read_bytes()
pins=json.loads((b/'adapter-pins.json').read_text());assert sha(b/'tools/Discriminant.lean')==pins['backend_generator_sha256']
subprocess.run([sys.executable,str(base/'tools/prefix-discriminant-bridge.py'),'--check'],check=True)
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS: retained collision, exact naming adapter, unchanged dependent sources, five field laws, eight green focused receipts')
