#!/usr/bin/env python3
"""Audit focused complete payment inverse evidence without replaying Lean."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=load(E/'s6-payment-inverse-targets.json')['targets'];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-payment-inverse-import-pins.json');reports=0
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
source=(S/'S6SourcePaymentAcceptedInverseV1.lean').read_text()
for variant in ['transfer','withdrawal']:
 assert 'theorem '+variant+'_accepted_inverse' in source
assert source.count('(accepted : decode_pool_v1_')==2
assert source.count('∃ encoded : Array U8 216#usize, encoded.val=bytes.val ∧')==2
assert '(ops' not in source
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,complete_transfer_216_inverse=True,complete_withdrawal_216_inverse=True,complete_1880_roundtrip=False,actual_sdk_binding=False,whole_s6_closed=False)))
