#!/usr/bin/env python3
"""Audit focused complete native afterstate codec evidence without replaying Lean."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=load(E/'s6-native-afterstate-codec-targets.json')['targets'];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-native-afterstate-codec-import-pins.json');reports=0
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
source=(S/'S6NativeAfterstateCodecV1.lean').read_text()
for theorem in ['decode_total','encode_total','accepted_frames','accepted_inverse','accepted_roundtrip']:
 assert 'theorem '+theorem in source
assert 'ReferenceAfterstate' not in source and '(ops' not in source
inverse=source[source.index('theorem accepted_inverse'):source.index('/-- Two-success')]
assert '(accepted : decode_pool_v1_pair_verified_afterstate_v1 bytes=' in inverse
assert '∃ encoded : Array U8 688#usize, encoded.val=bytes.val' in inverse
assert '(encoded_actual' not in inverse
manifest=load(E/'s6-native-afterstate-codec-targets.json')
assert manifest['native_afterstate_codec_closed_in_extracted_semantics']
assert not manifest['full_forest_closed'] and not manifest['actual_sdk_binding'] and not manifest['whole_s6_closed']
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,native_afterstate_decoder_total=True,native_afterstate_encoder_total=True,native_decode_only_inverse=True,full_forest_closed=False,actual_sdk_binding=False,whole_s6_closed=False)))
