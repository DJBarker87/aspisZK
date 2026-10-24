#!/usr/bin/env python3
"""Audit source-only concrete outer inverse evidence; no SDK closure claim."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s6-outer-native-codec-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-outer-native-codec-import-pins.json');reports=0
for target,attempt in m['targets'].items():
 r=load(E/attempt/'receipt.json');src=S/(target+'.lean')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 assert sha(src)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',src.read_text(),re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
assert m['concrete_outer_accepted_inverse'] and m['both_variants'] and m['all_1880_bytes']
assert not m['current_sdk_binding'] and not m['whole_s6_closed']
source=(S/'S6OuterNativeCodecV1.lean').read_text()
assert '(accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))' in source
assert 'AspisS6OuterNativeInstalled.encode statement=ok (.Ok encoded) ∧ encoded.val=bytes.val' in source
assert '(ops :' not in source and '(valid :' not in source and '(late :' not in source and '(pay :' not in source
for path,expected in load(E/'s6-outer-native-codec-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
for name,expected in load(E/'s6-outer-native-codec-source-pins.json')['reused_packets'].items():assert sha(E/name)==expected
for script in ['check-outer-native-binding.py','check-native-forest-decoder.py']:
 subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023'/script)],cwd=R,check=True,stdout=subprocess.DEVNULL)
print(json.dumps(dict(targets=len(m['targets']),standard_or_empty_axiom_reports=reports,concrete_outer_accepted_inverse=True,all_1880_bytes=True,current_sdk_binding=False,whole_s6_closed=False)))
