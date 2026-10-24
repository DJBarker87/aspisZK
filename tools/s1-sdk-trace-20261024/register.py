#!/usr/bin/env python3
"""Register focused, already checked S1 SDK trace targets; does not compile."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]; B=R/'docs/research/100bit-spend-path-20261013'; E=B/'evidence/s126-current-caller-20261021'; S=B/'lean-candidates/s126-caller-boundary-20261021'; P=E/'s1-sdk-prepared-trace-20261024'
P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets={'S1NativeBufferClaimTraceV1':'s1-native-buffer-claim-trace-v1','S1PreparedScratchCallsV1':'s1-prepared-scratch-calls-v1','S1NativeBufferPreparedTraceV1':'s1-native-buffer-prepared-trace-v4','S1SdkPreparedClaimTraceV1':'s1-sdk-prepared-claim-trace-v1'}
m=json.loads((E/'accepted-targets.json').read_text()); receipts=[]
for n,a in targets.items():
 r=json.loads((E/a/'receipt.json').read_text()); assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']
 m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']}; m['targets'][n]['receipt']=a+'/receipt.json'; receipts.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in receipts),max_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=0,axiom_reports=sum(len(r['print_axioms']) for r in receipts))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,rejected=['s1-native-buffer-prepared-trace-v1','s1-native-buffer-prepared-trace-v2','s1-native-buffer-prepared-trace-v3'],scope='Accepted original SDK first -> EVERY matching published SourceCuts -> same Prepared.new, early powers, borrowed claim scratch, numeric and joint trace. Standing SDK/Std/runtime/extraction, partial base Ops/Finish B and trace interpretation boundaries remain. Not native allocation/full-loop/terminal closure or oracle-law transport.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps({str(p.relative_to(R)):sha(p) for p in [R/'tools/s1-sdk-trace-20261024/register.py',R/'tools/s1-sdk-trace-20261024/check.py',R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py']},indent=2)+'\n')
print(json.dumps(metrics))
