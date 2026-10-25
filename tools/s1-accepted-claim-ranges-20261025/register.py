#!/usr/bin/env python3
"""Register focused, already checked S1 SDK trace targets; does not compile."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]; B=R/'docs/research/100bit-spend-path-20261013'; E=B/'evidence/s126-current-caller-20261021'; S=B/'lean-candidates/s126-caller-boundary-20261021'; P=E/'s1-accepted-claim-ranges-20261025'
P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets={'S1ClaimAcceptedScalarRangesV1':'s1-claim-accepted-scalar-ranges-v3','S1ClaimAcceptedCellsV1':'s1-claim-accepted-cells-v3','S1ClaimAcceptedCallerRangesV1':'s1-claim-accepted-caller-ranges-v2','S1SdkClaimInputRangesV1':'s1-sdk-claim-input-ranges-v3'}
m=json.loads((E/'accepted-targets.json').read_text()); receipts=[]
for n,a in targets.items():
 r=json.loads((E/a/'receipt.json').read_text()); assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']
 m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']}; m['targets'][n]['receipt']=a+'/receipt.json'; receipts.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in receipts),max_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=0,axiom_reports=sum(len(r['print_axioms']) for r in receipts))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,rejected=['s1-claim-accepted-scalar-ranges-v1','s1-claim-accepted-cells-v1','s1-sdk-claim-input-ranges-v1'],scope='Accepted-only: same original SDK acceptance/selected full cut/prepare/scratch/borrowed claim now derives all87 Claims cells four-word canonical ranges from concrete checked-Q guards. Same prior hypotheses and every prior conclusion retained. Native Claims initialization/totality/Terminal/Std/effects/source/release remain open.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps({str(p.relative_to(R)):sha(p) for p in [R/'tools/s1-accepted-claim-ranges-20261025/register.py',R/'tools/s1-accepted-claim-ranges-20261025/check.py',R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py']},indent=2)+'\n')
print(json.dumps(metrics))
