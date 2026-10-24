#!/usr/bin/env python3
"""Register only checked source targets; retain SDK import failures separately."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-first-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets={'S6CurrentStage1FirstFieldsV1':'s6-current-stage1-first-fields-v1','S1OwnedStage1AccountNumericV1':'s1-owned-stage1-account-numeric-v1'}
m=json.loads((E/'accepted-targets.json').read_text());receipts=[]
for name,attempt in targets.items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['target']==name
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 assert r['print_axioms'] and all('sorryAx' not in a for a in r['print_axioms'])
 m['targets'][name]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][name]['receipt']=attempt+'/receipt.json';receipts.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
failures=[]
for a in ['s6-sdk-stage1-reuse-v1','s6-sdk-stage1-reuse-v2','s6-sdk-public-read-v1','s6-sdk-entry-import-probe-v1']:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']!=0
 failures.append(dict(attempt=a,**{k:r[k] for k in ['target','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps']},selected=False))
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in receipts),max_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),axiom_reports=sum(len(r['print_axioms']) for r in receipts))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,rejected=failures,scope='ACCEPTED-ONLY complete owned source stage1: same account reads, decoded-public reuse and same preparation/range witnesses. Actual SDK theorem remains unchecked; no whole S1/S6 or native/ELF/security claim.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(R)):sha(p) for p in (R/'tools/s6-sdk-first-20261024').glob('*.py')},reused={str(p.relative_to(R)):sha(p) for p in [R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py']}),indent=2)+'\n')
print(json.dumps(metrics))
