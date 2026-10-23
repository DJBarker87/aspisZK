#!/usr/bin/env python3
"""Audit focused native parent encoder and validator totality evidence without replaying Lean."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=load(E/'s6-native-parent-total-targets.json')['targets'];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-native-parent-total-import-pins.json');reports=0
for target,attempt in rows.items():
 r=load(E/attempt/'receipt.json');assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 source=S/(target+'.lean');assert sha(source)==sha(E/attempt/'source.lean')==r['source_sha256']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
for name,function in [('S6NativeSnapshotEncodeTotalV1','encode_pool_v1_pair_live_snapshot_v1'),('S6NativeLateEncodeTotalV1','encode_pool_v1_pair_late_public_statement_v1')]:
 source=(S/(name+'.lean')).read_text()
 assert 'theorem encode_total' in source and function+' ' in source
 assert 'result.2.length=output.length' in source
 assert '(ops' not in source
source=(S/'S6NativeForestValidatorTotalV1.lean').read_text()
assert 'theorem validate_total' in source
manifest=load(E/'s6-native-parent-total-targets.json')
assert manifest['original_snapshot_encoder_total'] and manifest['original_transition_encoder_total'] and manifest['original_forest_validator_total']
assert not manifest['outer_forest_encoder_total'] and not manifest['whole_s6_closed']
discovery=load(E/'s6-native-forest-outer-discovery-v1.json')
assert not discovery['outer_encoder_present_in_legacy'] and not discovery['whole_native_encoder_total_claimed']
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,original_snapshot800_encoder_total=True,original_transition1520_encoder_total=True,original_forest_validator_total=True,outer_forest_encoder_total=False,whole_s6_closed=False)))
