"""Permanent final carrier-generation pass: enum-qualified Aeneas instances.
Run after carrier regeneration; --check rejects every remaining anonymous reader.
Uses the pinned generator unchanged except for its generated instance declId,
following research 317a687e34. No enum, tag, type or reader body is changed.
"""
from pathlib import Path
import subprocess,sys,hashlib,json
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
E=Path('evidence/pv-batch2-20261027/batch2d')
base=subprocess.check_output(['git','show','317a687e34:docs/research/100bit-spend-path-20261013/lean/ImportUnionNamedDiscriminant.lean'],text=True)
base=base.replace('ImportUnionNamedDiscriminant','PV_B2_D_NamedDiscriminant').replace('import_union_discriminant','pv_b2_discriminant').replace('namedDiscriminant','pvB2NamedDiscriminant')
outputs={L/'PV_B2_D_NamedDiscriminant.lean':base}
for p in sorted(L.glob('PV_B2_C_*.lean')):
 s=p.read_text()
 if '@[discriminant ' not in s and '@[pv_b2_discriminant ' not in s:continue
 s=s.replace('@[discriminant ','@[pv_b2_discriminant ')
 if 'import R1Z.PV_B2_D_NamedDiscriminant\n' not in s:
  pos=s.index('import ')
  s=s[:pos]+'import R1Z.PV_B2_D_NamedDiscriminant\n'+s[pos:]
 outputs[p]=s
assert len(outputs)==4, list(outputs)
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
r=dict(reference_commit='317a687e34',adapter='Pinned generateReadDiscriminantCmds; replace only instance declId with enum-qualified name',outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
if '--check' not in sys.argv:(E/'DISCRIMINANT-GENERATOR.json').write_text(json.dumps(r,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(outputs),'modules')
