#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-first-factor-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'tools/s6-sdk-first-20261024/factor.py'),'--check'],check=True)
targets={'S6SdkDependencyFactorV1':'s6-sdk-dependency-factor-v2','S6SdkStage1ReuseFactoredV1':'s6-sdk-stage1-reuse-factored-v1','S1SdkStage1AccountNumericV1':'s1-sdk-stage1-account-numeric-v1'}
m=json.loads((E/'accepted-targets.json').read_text());recs=[]
for name,a in targets.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['target']==name and r['print_axioms']
 assert sha(S/(name+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']
 m['targets'][name]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][name]['receipt']=a+'/receipt.json';recs.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in recs),max_rss_bytes=max(r['peak_rss_bytes'] for r in recs),swaps=sum(r['swaps'] for r in recs),axiom_reports=sum(len(r['print_axioms']) for r in recs))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,rejected=['s6-sdk-dependency-factor-v1'],scope='ACCEPTED-ONLY SDK interpreted first wrapper: concrete S6 codec/first installation and same S1 account/preparation/numeric witnesses. Exact declaration dependency factor; SDK/std/runtime/extraction trust retained. Original full-module/ALL14/coherent release re-pin and remaining S1 instances not closed.'),indent=2)+'\n')
files=['factor.py','register-factor.py','check-factor.py'];(P/'tools.json').write_text(json.dumps({str((R/'tools/s6-sdk-first-20261024'/f).relative_to(R)):sha(R/'tools/s6-sdk-first-20261024'/f) for f in files},indent=2)+'\n')
print(json.dumps(metrics))
