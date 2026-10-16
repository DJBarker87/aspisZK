#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
b=Path(__file__).resolve().parent;root=b.parents[4];base=root/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
green={'strict-low-c':('ExtractedRecordStrictLow',2),'strict-payload-b':('ExtractedPrefixStrictPayload',3)}
attempts=['strict-low-'+x for x in 'abc']+['strict-payload-'+x for x in 'ab']
for a in attempts:
 d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==(0 if a in green else 1),a
 assert r['source_sha256']==sha(d/'source.lean'),a
 assert r['runner_sha256']==sha(d/'runner.py'),a
 assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json')),a
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['memory_events_before']==r['memory_events_after']
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
 assert r['runtime_sha256'] and '4.32.0' in r['lean_version']
 if a in green:
  module,count=green[a];assert (base/'lean'/f'{module}.lean').read_bytes()==(d/'source.lean').read_bytes()
  log=(d/'lean.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
  assert len(reports)==count,(a,reports)
  for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
  assert 'sorryAx' not in log and 'error:' not in log and '_native.' not in log,a
entries=json.loads((b/'payload-cache-provenance/inventory.json').read_text())
assert len(entries)==8
for entry in entries:
 p=b/'payload-cache-provenance'/(entry['module']+'.json');r=json.loads(p.read_text())
 assert sha(p)==entry['receipt_sha256']
 assert r['exit_status']==0 and not r['dependency_build']
 assert r['source_manifest_entry']['source_sha256']==entry['source_sha256']
 assert sha(root/entry['current_source'])==entry['source_sha256']
 assert r['objects']['.olean']['sha256']==entry['object_sha256']
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS: two green targets/five standard-only audits; three failed checks retained; eight exact-source cache receipts; runtime/resource/artifact pins')
