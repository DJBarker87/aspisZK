#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-source-cuts-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'tools/s6-sdk-first-20261024/source-cuts.py'),'--check'],check=True)
targets={'S6SdkSourceCutTypesV1':'s6-sdk-source-cut-types-v1','S6SdkSourceCutReuseV1':'s6-sdk-source-cut-reuse-v2','S6SdkEnclosingCutsV1':'s6-sdk-enclosing-cuts-v1','S1SdkSourceCutNumericV1':'s1-sdk-source-cut-numeric-v1','S6SdkFirstObjectEquivalenceV1':'s6-sdk-first-object-equivalence-v3','S6SdkOriginalObjectCallerV1':'s6-sdk-original-object-caller-v2'}
m=json.loads((E/'accepted-targets.json').read_text());recs=[]
for n,a in targets.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']
 if n!='S6SdkSourceCutTypesV1':assert r['print_axioms']
 m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json';recs.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in recs),max_rss_bytes=max(r['peak_rss_bytes'] for r in recs),swaps=sum(r['swaps'] for r in recs),axiom_reports=sum(len(r['print_axioms']) for r in recs))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,rejected=['s6-sdk-source-cut-reuse-v1','s6-sdk-first-object-equivalence-v1','s6-sdk-first-object-equivalence-v2','s6-sdk-original-object-caller-v1'],scope='One accepted SDK wrapper supplies concrete S6 decoded-public reuse and S1 preparation/numeric on EVERY published enclosing SourceCuts, not independent witnesses. Existing SDK/std/runtime/extraction boundaries and partial S1 B/ops retained; coherent original-module/release join remains. f.semantic selection identity is neither assumed nor concluded.'),indent=2)+'\n')
files=['source-cuts.py','register-cuts.py','check-cuts.py','declaration-audit.py'];(P/'tools.json').write_text(json.dumps({str((R/'tools/s6-sdk-first-20261024'/f).relative_to(R)):sha(R/'tools/s6-sdk-first-20261024'/f) for f in files},indent=2)+'\n')
(P/'reused.json').write_text(json.dumps({str(p.relative_to(R)):sha(p) for p in [R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py',E/'s6-sdk-first-factor-20261024/declarations.json',E/'s6-sdk-first-factor-20261024/targets.json',S/'S6SdkDependencyFactorV1.lean',S/'S1OwnedStage1AccountNumericV1.lean']},indent=2)+'\n')
print(json.dumps(metrics))
