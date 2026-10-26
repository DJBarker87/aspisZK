"""Validate evidence and count invocations without claiming native refinement."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
corrections={x['attempt']:x for x in json.loads((P/'BEg_revision_corrections.json').read_text())}
receipts=[]
for p in sorted(P.glob('BEg_*/receipt.json')):
 x=json.loads(p.read_text())
 if x['attempt'] in corrections:
  x['receipt_source_anchor']=x['source_revision']
  x['source_revision']=corrections[x['attempt']]['worktree_revision_at_admission']
 receipts.append(x)
 for source,h in x['source_hashes'].items():assert sha(p.parent/'sources'/source)==h,(p,source)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if x['exit_status']==0 and x['kind']=='lean':
  assert x['swaps']=='0',p
  for line in x['print_axioms']:
   m=re.search(r'\[([^\]]*)\]',line)
   if m:assert set(m[1].replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'},(p,line)
lean=[r for r in receipts if r['kind']=='lean'];kani=[r for r in receipts if r['kind']=='kani']
assert len(lean)<=100 and len(kani)<=30
current={}
for f in sorted((R/'lean').glob('BEg_*.lean')):
 matching=[r['attempt'] for r in lean if r['exit_status']==0 and r['source_hashes'].get(f.name)==sha(f)]
 current[f.name]=matching
failures=[r['attempt'] for r in receipts if r['exit_status']!=0]
baseline=json.loads((P/'BEg_BASELINE.json').read_text())
for p,h in baseline['pins'].items():assert sha(R/p)==h,p
summary=dict(budget_used=dict(lean=len(lean),kani=len(kani)),lean_pass=sum(r['exit_status']==0 for r in lean),kani_pass=sum(r['exit_status']==0 for r in kani),failures=failures,current_lean_sources=current,unchecked_current=[k for k,v in current.items() if not v],max_success_rss_kib=max(int(r['peak_rss_kib']) for r in receipts if r['exit_status']==0),lean_wall_seconds=sum(r['wall_seconds'] for r in lean),native_association='NOT ESTABLISHED; L166 retained',distinct_delta=dict(T=0,P=0,G=0,C=0))
(P/'BEg_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'BEg_attempts.jsonl').write_text(''.join(json.dumps({k:r[k] for k in ['attempt','kind','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']})+'\n' for r in receipts))
print(json.dumps({k:v for k,v in summary.items() if k!='current_lean_sources'},indent=2))
