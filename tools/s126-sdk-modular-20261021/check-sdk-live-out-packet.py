#!/usr/bin/env python3
"""Validate excluded SDK output-slot experiments and retained counterexample."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-live-out';load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(P/'manifest.json');assert {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}==set(m['files'])|{'manifest.json'}
for name,d in m['files'].items():assert sha(P/name)==d,name
q=load(P/'qualification.json');assert len(q['targets'])==10
assert not any(x['semantic_accepted'] for x in q['targets'].values())
for tag,row in q['targets'].items():
 i=load(P/(tag+'-input.json'));r=row['receipt'];assert sha(P/'sources'/row['source']/'src/lib.rs')==i['source_sha256']==row['source_sha256']
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 if row['kind']=='codegen-only':assert r['exit_status']==0 and '--only-codegen' in i['command']
 else:assert r['exit_status']!=0
log=(P/'receipts/sdk-live-out-shared-bridge-v7/stdout.log').read_text();assert '2 of 830 failed' in log and '2 of 3 cover properties satisfied' in log
assert 'attempt to subtract with overflow' in log and 'unsafe{(*counter).get()} == initial' in log
r=load(P/'receipts/sdk-live-out-shared-bridge-counterexample-v7/receipt.json');assert r['exit_status']==10 and r['swaps']==0
j=load(P/'receipts/sdk-live-out-shared-bridge-counterexample-v7/stdout.log');failed=[r for x in j for r in x.get('result',[]) if r.get('status')=='FAILURE'];assert len(failed)==1 and failed[0]['trace']
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in P.rglob('*'))
print(json.dumps(dict(semantic_accepted=0,excluded_attempts=10,codegen_only_success=1,conditional_bridge_failed=True,counterexample_retained=True,native_sdk_closed=False)))
