#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-claims-row-step-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets={'S1ClaimsOwnedStepTypesV1':'s1-claims-owned-step-types-v1','S1ClaimsOwnedStepFunsV1':'s1-claims-owned-step-funs-v1','S1ClaimsOwnedStepExactV1':'s1-claims-owned-step-exact-v6'}
m=json.loads((E/'accepted-targets.json').read_text());rs=[]
for name,attempt in targets.items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 if name!='S1ClaimsOwnedStepTypesV1':assert r['print_axioms'] and all('sorryAx' not in a for a in r['print_axioms'])
 m['targets'][name]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][name]['receipt']=attempt+'/receipt.json';rs.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in rs),max_rss_bytes=max(r['peak_rss_bytes'] for r in rs),swaps=sum(r['swaps'] for r in rs),axiom_reports=sum(len(r['print_axioms']) for r in rs))
(P/'lean-targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,scope='Concrete extracted owned step TOTAL on bounded row indices; finite normal-decoder-result composition by induction and all-three-row reconstruction. No native uninitializedness, allocation/cleanup, full Claims/source-caller or security closure.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(R)):sha(p) for p in (R/'tools/s1-claims-row-step-20261024').glob('*.py')},rust={str(p.relative_to(R)):sha(p) for p in (R/'tools/s1-claims-row-step-20261024').glob('*.rs')},source_parent_revision=subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip(),reused={str(p.relative_to(R)):sha(p) for p in [R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-host-admission-20261024/HostAdmission.py']}),indent=2)+'\n')
print(json.dumps(metrics))
