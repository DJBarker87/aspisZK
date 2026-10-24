#!/usr/bin/env python3
"""Audit focused native transition codec evidence; no release closure claim."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=load(E/'s6-outer-native-total-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-outer-native-total-import-pins.json');reports=0
for target,attempt in manifest['targets'].items():
 r=load(E/attempt/'receipt.json');source=S/(target+'.lean')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 assert sha(source)==sha(E/attempt/'source.lean')==r['source_sha256']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023/check-outer-native-binding.py')],check=True)
assert manifest['outer_encoder_total'] and not manifest['free_ops_parameter'] and not manifest['child_success_premises']
assert not manifest['outer_inverse'] and not manifest['current_sdk_binding'] and not manifest['whole_s6_closed']
source=(S/'S6OuterNativeEncodeTotalV1.lean').read_text()
assert 'nativeOps statement ⦃ _ => True ⦄' in source
body=source[source.index('theorem encode_total'):source.index('#print axioms')]
assert '∃ result, AspisS6OuterNativeInstalled.encode statement=ok result' in body
assert '(ops :' not in body and '(accepted :' not in body and '(valid' not in body
for path,expected in load(E/'s6-outer-native-total-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
print(json.dumps(dict(targets=len(manifest['targets']),standard_or_empty_axiom_reports=reports,outer_encoder_total=True,child_success_premises=False,outer_inverse=False,current_sdk_binding=False,whole_s6_closed=False)))
