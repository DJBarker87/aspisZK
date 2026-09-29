#!/usr/bin/env python3
"""Reuse retained R70/R71 proof scripts in the actual R72 source namespace.

Only identifier renaming and deletion of the unavailable diagnostic probe
corollary are permitted. Original extraction and proof files stay unchanged.
Emit an apply_patch input, or check the exact generated files.
"""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--patch',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent
names=['ExplicitWord','ProductExecution','ProductCorrectness','CircleScalarTransport',
       'CircleFieldExecution','CircleSourceExecution']
mapping={n:'SamplerClosure'+n for n in names}
mapping['AspisR69Explicit']='AspisR72Sampler'
pattern=re.compile(r'\b('+'|'.join(mapping)+r')\b')
header='/- Mechanically reused R70/R71 proof script for the actual R72 closure.\nOnly identifier renaming and removal of the absent diagnostic-probe corollary.\nChecked by tools/generate_r78_closure.py; original files are preserved. -/\n'
pins={};patch=['*** Begin Patch']
for n in names:
    old=root/'lean/AspisV8R19'/(n+'.lean')
    source=old.read_text();pins[str(old.relative_to(root))]=hashlib.sha256(old.read_bytes()).hexdigest()
    if n=='CircleSourceExecution':
        probe='''theorem entry_execution (t : field.QM31) (hc : Canonical t) :
    circle_probe t = .ok (encodeResult (SamplerCirclePolicy.pureMap (decode t))) :=
  source_execution t hc
'''
        assert source.count(probe)==1
        source=source.replace(probe,'')
        assert source.count('#print axioms entry_execution\n')==1
        source=source.replace('#print axioms entry_execution\n','')
    new=header+pattern.sub(lambda m:mapping[m[0]],source)
    target=root/'lean/AspisV8R19'/(mapping[n]+'.lean')
    if a.patch:
        assert not target.exists(),target
        patch.append('*** Add File: '+str(target))
        patch.extend('+'+line for line in new.splitlines())
    else:assert target.read_text()==new,target
patch.append('*** End Patch')
if a.patch:print('\n'.join(patch))
else:print(json.dumps({'status':'PASS','transformation':'identifiers only; absent probe corollary removed',
    'original_proof_pins':pins,'targets':list(mapping.values())[:-1]},indent=2))
