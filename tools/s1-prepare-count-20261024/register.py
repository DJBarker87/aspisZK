#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
names={'S1PrepareBudgetCoreV1':'s1-prepare-budget-core-v2','S1PrepareBudgetTacticV1':'s1-prepare-budget-tactic-v7','S1SemanticBudgetV1':'s1-semantic-budget-v5-final-meta','S1PreparedBudgetV1':'s1-prepared-budget-v2','S1CurrentPrepareBudgetV1':'s1-current-prepare-budget-v2-final-imports','S1TopPrepareBudgetV1':'s1-top-prepare-budget-v2-final-imports'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rs=[];m=json.loads((E/'accepted-targets.json').read_text())
for n,a in names.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['target']==n and r['exit_status']==0,n
 assert sha(S/(n+'.lean'))==r['source_sha256'],n
 assert sha(Path('/tmp/s126-current-caller-20261021-objects')/(n+'.olean'))==r['object_sha256'],n
 assert r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms']),n
 rs.append(r);m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json'
metrics={'targets':len(names),'wall_seconds':sum(r['wall_seconds'] for r in rs),'max_rss_bytes':max(r['peak_rss_bytes'] for r in rs),'swaps':sum(r['swaps'] for r in rs)}
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
(E/'s1-prepare-count-targets.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','targets':names,'metrics':metrics,'qualification':'All-response/all-outcome source-model complete release op7 bound 115, combined with effects/full Result. Not actual native SDK/primitive correspondence, LocalBudgets for Some observer, whole-driver 1161 or release security closure.'},indent=2)+'\n')
failures=[]
for glob in ['s1-prepare-budget-core-v*','s1-prepare-budget-tactic-v*','s1-semantic-budget-v*','s1-prepared-budget-v*','s1-current-prepare-budget-v*','s1-top-prepare-budget-v*','s1-semantic-budget-sample-probe-v*','s1-budget-bind-probe-v*']:
 for p in sorted(E.glob(glob+'/receipt.json')):
  r=json.loads(p.read_text())
  if r['exit_status']!=0:failures.append({'receipt':str(p.relative_to(E)),**{k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','source_sha256']}})
(E/'s1-prepare-count-failures.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':failures,'explanation':'Tactic elaboration/proof composition failures only. Failed targets and generated sorryAx reports are not accepted. Continuation goal scoping, typed child selection and let/projection reduction were fixed; no resource defaults changed.'},indent=2)+'\n')
(E/'s1-prepare-count-tool-pins.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','scripts':{str(p.relative_to(R)):sha(p) for p in sorted((R/'tools/s1-prepare-count-20261024').glob('*.py'))}},indent=2)+'\n')
print(json.dumps(metrics))
