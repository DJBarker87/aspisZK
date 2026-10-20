#!/usr/bin/env python3
"""Check selected raw-to-bound prefix and exact production source cuts; no Lean replay."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
R=D.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
t=(D/'diagnostics/alternate-generated/AspisR1CurrentPowers/Types.lean').read_text()
f=(D/'diagnostics/alternate-generated/AspisR1CurrentPowers/Funs.lean').read_text()
t=t[t.index('namespace AspisR1CurrentPowers')+len('namespace AspisR1CurrentPowers'):t.rindex('end AspisR1CurrentPowers')]
a=f.index('/-- [aspis_r1_current_powers::field::');b=f.index('/-- [aspis_r1_current_powers::weights::powers::{impl');const=f[a:b]
a=b;b=f.index('/-- Trait implementation:',a);cb=f[a:b]
cb=cb.replace('{N : Std.Usize}','(mul : field.WideExact → field.WideExact → Result field.WideExact) {N : Std.Usize}').replace('field.WideExact.mul a we','mul a we').replace('      c i','      mul c i')
prefix='import Aeneas\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace AspisR1CurrentPowers\n'+t+const+cb
model=(D/'sources/CurrentPowersCallback.lean').read_text()
assert model.startswith(prefix)
assert model[len(prefix):].lstrip().startswith('theorem call_once_of_mul')
pins=json.loads((D/'extraction-input/source-pins.json').read_text())
for name,h in pins['kit_files'].items():assert sha((D/'extraction-input'/name).read_bytes())==h,name
for cut in pins['cuts']:
 raw=subprocess.check_output(['git','-C',str(R),'show',pins['revision']+':'+cut['path']])
 assert sha(raw)==cut['file_sha256']
 assert sha(raw[cut['start_byte']:cut['end_byte_exclusive']])==cut['sha256']
assert 'def field.WideExact.mul' not in f
external=(D/'diagnostics/alternate-generated/AspisR1CurrentPowers/FunsExternal_Template.lean').read_text()
assert 'axiom field.WideExact.mul' in external
print(json.dumps({'status':'PASS','production_cuts':len(pins['cuts']),'revision':pins['revision'],'retained_prefix_sha256':sha(prefix.encode()),'scope':'Exact callback/type/constant prefix under explicit mul parameter; full FnMut/from_fn NOT accepted'},indent=2))
