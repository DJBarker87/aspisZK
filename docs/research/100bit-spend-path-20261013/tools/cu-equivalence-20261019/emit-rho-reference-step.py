#!/usr/bin/env python3
"""Reuse source-identical nominal carriers and bind unchanged actual arithmetic."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
raw=(here/'rho-reference-step-generated/Funs.lean').read_bytes()
assert b'fail panic' not in raw and b'import AspisR1RhoReference.FunsExternal' in raw
types=(here/'rho-reference-step-generated/Types.lean').read_text()
original=(area/'lean/extracted-qm31-arithmetic-20261015/AspisR1Qm31ArithmeticProbe/Types.lean').read_text()
for name in ['M31','CM31','QM31']:
    pattern=r'(?m)^(?:def|structure) field\.'+name+r'\b.*?(?=\n\n)'
    assert re.search(pattern,types,re.S)[0]==re.search(pattern,original,re.S)[0],name
prefix=b'''import ExtractedCurrentTowerAdd
namespace AspisR1RhoReference
abbrev field.M31 := AspisR1Qm31ArithmeticProbe.field.M31
abbrev field.CM31 := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev field.QM31 := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev field.M31.mul := AspisR1Qm31ArithmeticProbe.field.M31.mul
abbrev field.QM31.add := AspisR1Qm31ArithmeticProbe.field.QM31.add
end AspisR1RhoReference
'''
out=b'import Aeneas\n'+prefix+raw.replace(b'import Aeneas\n',b'').replace(b'import AspisR1RhoReference.Types\n',b'').replace(b'import AspisR1RhoReference.FunsExternal\n',b'')
p=area/'lean/AspisR1RhoReference/Funs.lean'
if args.check:assert p.read_bytes()==out
else:p.parent.mkdir(exist_ok=True);p.write_bytes(out)
print(json.dumps(dict(check=args.check,raw_funs_sha256=hashlib.sha256(raw).hexdigest(),promoted_sha256=hashlib.sha256(out).hexdigest(),complete_generated_bodies_unchanged=True)))
