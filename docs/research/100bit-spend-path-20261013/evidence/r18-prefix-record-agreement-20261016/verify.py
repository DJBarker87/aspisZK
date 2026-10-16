#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
b=Path(__file__).resolve().parent;root=b.parents[4];base=root/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
green={'loop-map-a':('ExtractedPrefixLoopMap',1),'record-agreement-d':('ExtractedPrefixRecordAgreement',5),'parser-agreement-b':('ExtractedPrefixParserAgreement',2)}
attempts=['loop-map-a']+['record-agreement-'+x for x in 'abcd']+['parser-agreement-'+x for x in 'ab']
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
 if a in green:
  module,count=green[a];assert (base/'lean'/f'{module}.lean').read_bytes()==(d/'source.lean').read_bytes()
  log=(d/'lean.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
  assert len(reports)==count,(a,reports)
  for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
  assert 'sorryAx' not in log and 'error:' not in log,a
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS: three green targets/eight standard-only audits, four retained local failures, exact source/runtime/resource pins')
