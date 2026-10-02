#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'formal.json').read_text())
rid='aspis-focus-1790960164935938000'
r=json.loads((root/'runs'/(rid+'.receipt.json')).read_text());log=(root/'runs'/(rid+'.log')).read_text()
assert r['exit_status']==0 and 'Exit status: 0' in log and 'error:' not in log
assert r['source_sha256']==sha(root/'R402Q22IndependentLaw.lean')==sha(root/'runs'/(rid+'.source.lean'))
assert r['runner_sha256']==sha(root/'run_focus.py')
for k in ['target','source_revision','source_sha256','exit_status','wall_time','peak_rss_kib','swaps','resources','complete_print_axioms']:assert m[k]==r[k],k
reports=re.findall(r"'([^\n]+)' depends on axioms: \[([\s\S]*?)\]",log)
assert len(reports)==3 and 'sorryAx' not in log
assert {x[0].rsplit('.',1)[-1] for x in reports}=={'loop_state_irrelevance','challenge_state_irrelevance','fresh_table_kernel'}
for name,axioms in reports:assert set(x.strip() for x in axioms.split(','))=={'propext','Classical.choice','Quot.sound'}
a=json.loads((root/'dependency-cache-audit.json').read_text())
for name,row in a['records'].items():
 assert row['source_sha256']==sha(root/'dependencies/AspisV8R19'/(name+'.lean'))==r['direct_local_import_sha256']['AspisV8R19.'+name]
 assert len(row['object_sha256'])==64 and row['object_size']>0
assert r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}
for line in (root/'SHA256SUMS').read_text().splitlines():
 expected,path=line.split('  ',1);assert sha(root/path)==expected,path
print('R402 evidence: PASS; three complete clean axiom reports')
