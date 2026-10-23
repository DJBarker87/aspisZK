#!/usr/bin/env python3
"""Audit accepted forward/reference restoration proofs and excluded paired query."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted=load(E/'accepted-targets.json')['targets'];pin=load(E/'reference-first-reuse-import-pins.json');count=0
for module,attempt in [('S2SdkReferenceFirstReuseV1','s2-sdk-reference-first-reuse-v4'),('S2SdkReadyAcquireV1','s2-sdk-ready-acquire-v3'),('S2SdkReadyStateV1','s2-sdk-ready-state-v2')]:
 r=load(E/attempt/'receipt.json');c=load(E/attempt/'command.json');assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(module+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']==c['source_sha256']==accepted[module]['source_sha256']==pin['targets'][module]['source_sha256']
 assert pin['targets'][module]['object_sha256']==r['object_sha256']
 assert '-j1' in c['command'] and '-M4400' in c['command']
 source=(S/(module+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',source,re.M)
 for report in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert m,report
  assert set(re.findall(r'[A-Za-z_.]+',m[1]))<= {'propext','Classical.choice','Quot.sound'},report;count+=1
 assert 'error:' not in (E/attempt/'lean.log').read_text()
assert count==12
P=E/'sdk-reference-first-native'
for rel,d in load(P/'manifest.json')['files'].items():assert sha(P/rel)==d,rel
assert not any(p.suffix in ['.out','.olean','.o','.rlib','.llbc','.pyc'] for p in P.rglob('*'))
assert load(P/'qualification.json')['accepted_kani_targets']==0
r=load(P/'receipts/sdk-native-reference-first-native-pair-v1/receipt.json');assert r['exit_status']==1 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
assert '180s deadline' in (P/'case/timeout.json').read_text()
print(json.dumps(dict(accepted_lean_targets=3,standard_axiom_reports=count,accepted_paired_kani_targets=0,excluded_pair='SSA timeout; no proof credit')))
