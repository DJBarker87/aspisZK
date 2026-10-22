#!/usr/bin/env python3
"""Audit constructive complete caller scope, source/receipt pins and axiom closure.
No unchanged Lean or Kani replay. Native SDK/SBF/ROM/TX2 instantiation is NOT
proved by this artifact checker or by the reference constructor alone.
"""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets=[('S2SdkKeyEqualityV1','s2-sdk-key-equality-v1'),('S2SdkReadyCallerV1','s2-sdk-ready-caller-v6'),('S2SdkReadyBodyV1','s2-sdk-ready-body-v6'),('S2SdkReadyStatementV1','s2-sdk-ready-statement-v2'),('S2SdkReadyOriginalV1','s2-sdk-ready-original-v2'),('S2SdkReadyRawInputsV1','s2-sdk-ready-raw-inputs-v1')]
accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'ready-caller-import-pins.json');reports=0
for module,attempt in targets:
 p=E/attempt;r=load(p/'receipt.json');c=load(p/'command.json');source=S/(module+'.lean')
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(source)==sha(p/'source.lean')==r['source_sha256']==c['source_sha256']==accepted[module]['source_sha256']==pins['targets'][module]['source_sha256']
 assert accepted[module]['receipt']==attempt+'/receipt.json' and r['object_sha256']==pins['targets'][module]['object_sha256']
 assert '-j1' in c['command'] and '-M4400' in c['command']
 assert 'error:' not in (p/'lean.log').read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',source.read_text(),re.M)
 for report in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert m,report
  assert set(re.findall(r'[A-Za-z_.]+',m[1]))<= {'propext','Classical.choice','Quot.sound'},report;reports+=1
assert reports==21
# Reuse three existing generic proofs verbatim, avoiding a cold unrelated
# protocol-model dependency build. Namespace/import changes are explicit.
old=(B/'lean/ExtractedTerminalEquality.lean').read_text();new=(S/'S2SdkKeyEqualityV1.lean').read_text()
assert old[old.index('local instance'):old.index('theorem m31_ne_spec')]==new[new.index('local instance'):new.index('#print axioms')]
raw=(S/'S2SdkReadyRawInputsV1.lean').read_text();sig=raw[raw.index('theorem construct ('):raw.index('\n    ∃ out,')]
assert len(re.findall(r'=\s*ok\b',sig))==4
for name in ['decoded','validated','encoded','firstReturned']:assert '('+name+' :' in sig
for name in ['accepted','run','bodyRun','scanned','compared','tagRead','proofAllowed','publicAllowed','commonRead','projected']:assert '('+name+' :' not in sig
for field in ['pMeta','uMeta','cMeta','cFree','proofCounter','publicCounter','checkpointZero','prefixBytes','tagByte']:assert '('+field+' :' in sig
assert 'state (triple pa ua ca) lamports p u c' in raw
assert '() none=ok (.Ok checkpointBytes)' in raw
original=load(E/'caller-source-adoption-overlay-20261022.json');overlay=load(E/'ready-caller-source-overlay-20261022.json')
for rel,d in overlay['files'].items():assert sha(R/rel)==d==original['files'][rel]['old_source_sha256']==original['files'][rel]['adopted_source_sha256']
for _,attempt in targets:
 assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc','.pyc'] for p in (E/attempt).rglob('*'))
print(json.dumps(dict(accepted_targets=len(targets),standard_axiom_reports=reports,remaining_call_observations=['decoded','validated','encoded','firstReturned'],native_sdk_closed=False,source_change=False)))
