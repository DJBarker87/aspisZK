#!/usr/bin/env python3
"""Export source/text only after the complete sequential run is terminal."""
from pathlib import Path
import json,sys,tarfile
W=Path(sys.argv[1]).resolve();destination=Path(sys.argv[2]).resolve()
sequence=json.loads((W/'rejection-sequence.json').read_text())['runs']
assert [r['case']for r in sequence]==['point'+str(i)for i in range(6)]
assert all(r['exit_status']==0 for r in sequence[:5])
assert sequence[-1]['exit_status']!=0
failed=W/'run-point5'
assert 'CBMC timed out'in(failed/'verify-stdout.log').read_text()
assert json.loads((failed/'verify-receipt.json').read_text())['exit_status']!=0
for point in [0,1,2,3,4,6]:
 a=W/('run-point'+str(point));r=json.loads((a/'verify-receipt.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']
 p=a/'linked-loop-postcheck.json'
 if point==6:p=W/'run-postcheck6/linked-loop-postcheck.json'
 assert json.loads(p.read_text())['all_four_checked_loop_ids_present']
negative=W/'run-negative';r=json.loads((negative/'verify-receipt.json').read_text())
assert r['exit_status']!=0
assert 'Failed Checks: assertion failed: !negative'in(negative/'verify-stdout.log').read_text()
allowed={'.rs','.toml','.lock','.json','.log','.py'}
with tarfile.open(destination,'w:gz')as archive:
 for p in sorted(W.rglob('*')):
  if not p.is_file()or'target'in p.relative_to(W).parts:continue
  if p.suffix not in allowed and p.suffix not in {'.v'+str(i)for i in range(1,9)}:
   raise RuntimeError('Unexpected non-source export input: '+str(p))
  archive.add(p,arcname=str(p.relative_to(W)))
print(str(destination))
