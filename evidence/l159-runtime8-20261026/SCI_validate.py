"""Validate SCI source/evidence correspondence without a prover replay."""
from pathlib import Path
import hashlib,json,re,collections
P=Path(__file__).resolve().parent; R=P.parents[1]
receipts=sorted(P.glob('SCI_[0-9][0-9][0-9]/receipt.json'))
assert len(receipts)<=100
records=[json.loads(p.read_text()) for p in receipts]
assert [r['attempt'] for r in records]==[f'SCI_{i:03}' for i in range(1,len(records)+1)]
for r in records:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert '-M7000' in r['command'] and '-j1' in r['command']
 for src,digest in r['source_hashes'].items():
  p=P/r['attempt']/'sources'/src
  assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
 if r['exit_status']==0:
  assert r['print_axioms']
  assert all('sorryAx' not in line for line in r['print_axioms'])
for p in sorted((R/'lean').glob('SCI_*.lean')):
 text=p.read_text();digest=hashlib.sha256(p.read_bytes()).hexdigest()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)',text)
 matching=[r for r in records if r['exit_status']==0 and r['source_hashes'].get(p.name)==digest]
 assert matching,p.name
 final=matching[-1]
 for name in re.findall(r'^theorem\s+(\w+)',text,re.M):
  assert '#print axioms '+name in text,name
ledger=json.loads((P/'SCI_LEDGER_DELTA.json').read_text())
assert ledger['before']==ledger['after']
assert all(v==0 for row in ledger['delta'].values() for v in row.values())
assert (P/'SCI_BEFORE.lean.txt').read_bytes()==(P/'SCI_AFTER.lean.txt').read_bytes()==(R/'lean/Rc7_Top.lean').read_bytes()
print(json.dumps({'attempts':len(records),'passed':sum(r['exit_status']==0 for r in records),'failed':sum(r['exit_status']!=0 for r in records),'wall_seconds':sum(r['wall_seconds'] for r in records),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in records),'swaps':0,'actual_top_removed':0},indent=2))
