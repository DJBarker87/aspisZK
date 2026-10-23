#!/usr/bin/env python3
"""Source-only audit; no unchanged prover replay and no native-caller closure."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-scan-fission'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,digest in load(P/'manifest.json')['files'].items():assert sha(P/name)==digest,name
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in P.rglob('*'))
def body(s,name):
 a=s.index('fn '+name+'(');b=s.index('{',a)+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
old=(E/'sdk-native-constructor/source/src/lib.rs')
if not old.exists():
 matches=list((E/'sdk-native-constructor').rglob('lib.rs'));assert len(matches)==1;old=matches[0]
original=old.read_text()
cut=load(E/'sdk-native-constructor/source/source-cut.json')
fission=cut['scan_fission']

for mode,tag,checks in [('enter','sdk-native-scan-fission-enter-v1',2955),('leave','sdk-scan-fission-leave-check-v1',110)]:
 s=(P/'sources'/mode/'src/lib.rs').read_text();i=load(P/(tag+'-input.json'));row=load(P/'qualification.json')['targets'][tag];r=row['receipt']
 assert sha(P/'sources'/mode/'src/lib.rs')==i['source_sha256']==row['source_sha256']
 assert row['checks']==checks and row['covers']==2 and r['swaps']==0
 for name in ['stage1','scan_enter','scan_leave']:assert body(s,name)==body(original,name),name
 meta=load(P/'metadata'/mode/'harness-metadata.json');h=next(h for h in meta['proof_harnesses'] if h['pretty_name']==row['harness'])
 assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'scan_'+mode}}
 assert not h['attributes']['verified_stubs']
 depinput=load(P/('sdk-shared-prefix-codegen-scan-fission-enter-v1-input.json' if mode=='enter' else tag+'-input.json'))
 for dep,d in depinput['local_dependency_source_pins'].items():
  for name,digest in d['files'].items():assert sha(E/'sdk-native-constructor/dependencies'/dep/name)==digest,(dep,name)
 post=load(P/('sdk-shared-prefix-codegen-scan-fission-enter-v1-dependency-postcheck.json' if mode=='enter' else tag+'-dependency-postcheck.json'));assert post['unchanged'] and all(post['unchanged'].values())
 if mode=='enter':
  rows=load(P/'case/properties-complete.json');a=load(P/'case/scan-enter-audit.json');assert len(rows)==checks+2 and a['noncover_successes']==checks
  covers=set(a['reached_covers']);assert all(x['status']==('FAILURE' if x['property'] in covers else 'SUCCESS') for x in rows)
  assert any('--enforce-contract' in cmd and h['contract']['contracted_function_name'] in cmd for cmd in i['commands'])
 else:
  log=(P/'receipts'/tag/'stdout.log').read_text();assert '0 of 110 failed' in log and '2 of 2 cover properties satisfied' in log
# Exact fission collapse is checked below using the retained original/replacement.
replacement=fission.get('replacement',fission.get('instrumented'));oldexpr=fission.get('original')
assert replacement and oldexpr
stage=body(original,'stage1');assert stage.count(replacement)==1
assert stage.replace(replacement,oldexpr)==body((R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text(),'stage1')
m='S2SdkScanFissionV1';a='s2-sdk-scan-fission-v1';r=load(E/a/'receipt.json');pins=load(E/'scan-fission-import-pins.json')
assert r['exit_status']==0 and r['swaps']==0 and len(r['print_axioms'])==4
assert sha(B/'lean-candidates/s126-caller-boundary-20261021'/ (m+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][m]['source_sha256']
for report in r['print_axioms']:
 axioms=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert axioms
 assert set(re.findall(r'[A-Za-z_.]+',axioms[1]))<={'propext','Classical.choice','Quot.sound'}
print(json.dumps(dict(native_probe_checks=3065,reached_covers=4,axiom_reports=4,frozen_stage1_erasure=True,native_sdk_closed=False)))
