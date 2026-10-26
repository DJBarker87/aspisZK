"""Read-only validation of this scoped packet; launches no build or solver."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for p in sorted(P.glob('BEh_*/receipt.json')):
 r=json.loads(p.read_text())
 assert r['exit_status']==0,(p,r['exit_status'])
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and r['swaps']=='0'
 for name,digest in r['source_hashes'].items():
  assert sha(p.parent/'sources'/name)==digest
  assert sha(R/'lean'/name)==digest
 for line in r['print_axioms']:
  match=re.search(r'axioms: \[([^]]*)\]',line)
  if match:assert set(filter(None,match[1].split(', ')))<=allowed,(p,line)
 rows.append({k:r[k] for k in ['attempt','source_hashes','deps_fingerprint','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
assert len(rows)<=30 and len({r['attempt'] for r in rows})==len(rows)
for name,pin in json.loads((P/'BEh_source_pins.json').read_text()).items():
 assert sha(R/name)==pin['sha256'],name
assert (P/'BEh_BEFORE_Top.lean.txt').read_bytes()==(P/'BEh_AFTER_Top.lean.txt').read_bytes()==(R/'lean/Rc9_Top.lean').read_bytes()
ledger=json.loads((P/'BEh_recount.json').read_text())
assert ledger['before']==ledger['after']
assert ledger['distinct_delta']==dict(T=0,P=0,G=0,C=0)
for p in (R/'lean').glob('BEh_*.lean'):
 code=re.sub(r'/\-[\s\S]*?\-/','',p.read_text())
 code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',code),p
summary=dict(lean_attempts=len(rows),kani_runs=0,all_passed=True,axioms_audits=sum(len(r['print_axioms']) for r in rows),compiler_wall_seconds=sum(r['wall_seconds'] for r in rows),maximum_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,delta=ledger['distinct_delta'],actual_theorem=ledger['actual_theorem'],claim='Scoping only; L166 retained; no concrete native association proved')
(P/'BEh_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
(P/'BEh_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
