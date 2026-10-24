#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-finish-selectors-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
names={'S1FinishMaskSourceV1':'s1-finish-mask-source-v6','S1FinishFromFnStableV1':'s1-finish-from-fn-stable-v3','S1FinishSelectorsV1':'s1-finish-selectors-v4','S1FinishChildrenV1':'s1-finish-children-v6','S1TopPrepareFinishChildrenV1':'s1-top-prepare-finish-children-v1','S1OwnedStage1FinishChildrenV1':'s1-owned-stage1-finish-children-v1','S1FinishArithmeticTotalV1':'s1-finish-arithmetic-total-v1','S1SemanticFinishMaskCallsV1':'s1-semantic-finish-mask-calls-v1','S1FinishMaskProvenanceV1':'s1-finish-mask-provenance-v1'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((E/'accepted-targets.json').read_text());rs=[]
for n,a in names.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['target']==n
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']
 assert r['swaps']==0 and r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms'])
 m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json';rs.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(rs),wall_seconds=sum(r['wall_seconds'] for r in rs),max_rss_bytes=max(r['peak_rss_bytes'] for r in rs),swaps=sum(r['swaps'] for r in rs))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=names,metrics=metrics,native_target='finish_selectors_match_full_words-v2',qualification='Same accepted installed op7/owned stage1 with concrete round children and six fixed finish operations. Full claims producer and terminal evaluator remain explicit; native SDK/Std/abort, S9 callee association, release/coherent-source and security joins remain open.'),indent=2)+'\n')
failed=[]
for pattern in ['s1-finish-mask-source-v*','s1-finish-from-fn-stable-v*','s1-finish-selectors-v*','s1-finish-children-v*']:
 for d in sorted(E.glob(pattern)):
  p=d/'receipt.json'
  if p.exists():
   r=json.loads(p.read_text())
   if r['exit_status']!=0:failed.append(dict(attempt=d.name,**{k:r[k] for k in ['target','exit_status','source_sha256','wall_seconds','peak_rss_bytes','swaps']}))
  elif d.is_dir():failed.append(dict(attempt=d.name,status='not_launched',reason='Import preflight assertion after a failed namespace-cache generation; no Lean process started.'))
(P/'failures.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',attempts=failed,scope='Failed source/API/namespace and dependent-match attempts excluded from accepted evidence. Compiler error-recovery sorryAx logs are historical failures, not admitted source axioms. All retries changed source or resolved identified missing dependency/IR files. No OOM or cap increase.'),indent=2)+'\n')
files=[p for t in ['s1-finish-selectors-20261024','s1-finish-children-20261024'] for p in (R/'tools'/t).glob('*') if p.is_file()]
files+=[R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py']
(P/'tool-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(R)):sha(p) for p in sorted(files)}),indent=2)+'\n')
print(json.dumps(metrics))
