#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,tarfile
W=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((W/'manifest.json').read_text());archive=W/m['archive'];assert sha(archive.read_bytes())==m['archive_sha256']
with tarfile.open(archive) as t:
 sums={line.split('  ',1)[1]:line.split('  ',1)[0] for line in t.extractfile('SHA256SUMS').read().decode().splitlines()};assert len(sums)+1==m['archive_entries'];blobs={}
 for n,h in sums.items():
  b=t.extractfile(n).read();assert sha(b)==h,n;blobs[n]=b
 allhashes=set(sums.values());count=0
 for n,r in m['receipts'].items():
  assert json.loads(blobs[n])==r,n
  assert r['source_revision']==m['production_revision']
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
  assert r['process_swaps']==0 and r['cgroup_swap_current']==0
  assert r['source_pins_sha256'] in allhashes
  for path,h in r['outputs'].items():assert h in allhashes,(n,path,h)
  count+=1
 for n,b in blobs.items():
  if n.endswith('.llbc'):assert not json.loads(b)['has_errors'],n
 success=m['receipts']['prepared-helper-fields/runs/aeneas-a/receipt.json'];assert success['exit_status']==0
 assert 'PROPOSAL' in success['input_classification']
 a=json.loads((W/'prepared-proposal-audit.json').read_text());assert a['proposed_prepared_sha256']=='3fddfd4f2b0366f2f1f0c94153a6793df457b44f0ceda6eb13fcc96f4b31c8a1'
 print(f'PASS {len(sums)} pinned archive members, {count} extraction receipts; 1 successful proposal only, no Lean claim')
