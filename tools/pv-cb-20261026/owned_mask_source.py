"""Validate extracted field bodies and bind owned mask control to checked types."""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2]
rawpath=root/'evidence/pv-cb-20261026/owned-mask-rec-generated/Funs.lean'
curpath=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP7CurrentFieldSource.lean'
raw=rawpath.read_text();cur=curpath.read_text()
def defs(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'@\[.*?\]','',s,flags=re.S)
 return {m[1]:re.sub(r'\s+','',m[0].split('\nend ')[0]) for m in re.finditer(r'(?m)^def\s+(aspis_core\.[\w.]+)\b.*?(?=^def\s|^end\s|\Z)',s,re.S)}
a=defs(raw[:raw.index('def owned.mul_i')]);b=defs(cur)
assert len(a)==31
assert all(v.replace('31#i32','31#u32')==b.get(k) for k,v in a.items())
# Existing nominal carriers have identical fields. No runtime representation claim.
types=(rawpath.parent/'Types.lean').read_text()
for name,fields in [('CM31',['a : aspis_core.field.M31','b : aspis_core.field.M31']),('QM31',['c0 : aspis_core.field.CM31','c1 : aspis_core.field.CM31']),('PreparedQm31Multiplier',['components : Array (Array aspis_core.field.M31 3#usize) 3#usize'])]:
 block=types.split('structure aspis_core.field.'+name+' where\n')[1].split('/--')[0]
 assert [x.strip() for x in block.strip().splitlines()]==fields
body=raw[raw.index('def owned.mul_i'):raw.rindex('end PV_CB_OwnedMask')]
body=body.replace('aspis_core.field.','ProverRwP7CurrentFieldSource.aspis_core.field.')
out='import R1Z.ProverRwP7CurrentFieldSource\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 2048\nnamespace R1Z.PV_CB_OwnedMask\n'+body+'end R1Z.PV_CB_OwnedMask\n'
p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_OwnedMask.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
receipt=dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),checked_field_sha256=hashlib.sha256(cur.encode()).hexdigest(),field_definitions=sorted(a),normalization='31 field declarations whitespace-identical after two 31#i32 to31#u32 backend shift-count API edits; owned control bodies unchanged except qualified checked field names; nominal types matched field-for-field',native_correspondence='pending')
(rawpath.parent/'normalization.json').write_text(json.dumps(receipt,indent=2)+'\n')
