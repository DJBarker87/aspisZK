#!/usr/bin/env python3
"""Audit focused native encoder/reference decoder byte law evidence without replaying Lean."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'s6-native-afterstate-byte-law-targets.json');rows=manifest['targets'];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-native-afterstate-byte-law-import-pins.json');reports=0
for target,attempt in rows.items():
 r=load(E/attempt/'receipt.json');assert r['exit_status']==0 and r['swaps']==0
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 source=R/manifest['source_paths'][target];assert sha(source)==sha(E/attempt/'source.lean')==r['source_sha256']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
source=(S/'S6NativeAfterstateRoundtripV1.lean').read_text()
assert 'theorem accepted_roundtrip' in source
assert '(decoded : AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=' in source
assert '(encoded_actual : AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (native a)=' in source
assert ': encoded.val=bytes.val' in source
assert not manifest['whole_s6_closed'] and not manifest['actual_native_decoder_transport']
provenance=load(E/'s6-s2k-source-reuse/provenance.json')
assert all(row['byte_equal'] for row in provenance['local_source_comparison'].values())
assert provenance['remote_cache_is_not_release_evidence']
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,native_encoder_reference_decoder_bytes_equal=True,actual_native_decoder_transport=False,actual_sdk_binding=False,whole_s6_closed=False)))
