#!/usr/bin/env python3
"""Audit focused current codec/first/S1 parent composition, not SDK closure."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s126-current-caller-installation-targets.json');accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s126-current-caller-installation-import-pins.json');reports=0
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
assert m['current_codec_slots_concrete'] and m['enclosing_owned_stage1_value_join'] and m['s1_independent_first_premise_removed']
assert not any(m[n] for n in ['native_sdk_state_binding','native_claim_refinement','whole_s1_closed','whole_s6_closed'])
for path,expected in load(E/'s126-current-caller-installation-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
for name,expected in load(E/'s126-current-caller-installation-reused-pins.json')['packets'].items():assert sha(E/name)==expected
for script in ['materialize-current-caller.py','generate-current-adapter-carrier.py','generate-current-verifier-carrier.py']:
 subprocess.run(['python3',str(R/'tools/s6-full-forest-roundtrip-20261023'/script),'--check'],cwd=R,check=True,stdout=subprocess.DEVNULL)
# Exact forall scope required by the current caller's named codec interface.
source=(S/'S6CurrentCodecInstallationV1.lean').read_text()
assert '(decoded : (install ops).op47 original=ok (.Ok statement))' in source
assert '(encoded_actual : (install ops).op22 statement=ok (.Ok encoded))' in source
source=(S/'S6CurrentStage1FirstJoinV1.lean').read_text()
assert '(accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)' in source
assert 'FirstComposition.firstCurrent' in source and '(hfirst :' not in source
source=(S/'S1CurrentOwnedPreparedJoinV1.lean').read_text()
assert '(accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned' in source and '(hfirst :' not in source
print(json.dumps(dict(targets=len(m['targets']),standard_or_empty_axiom_reports=reports,current_codec_slots_concrete=True,enclosing_owned_stage1_value_join=True,s1_independent_first_premise_removed=True,native_sdk_state_binding=False,whole_s1_closed=False,whole_s6_closed=False)))
