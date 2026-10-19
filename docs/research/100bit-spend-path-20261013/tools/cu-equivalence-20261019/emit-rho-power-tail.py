#!/usr/bin/env python3
"""Keep raw suffix/carriers unchanged; bind only exact existing QM31 mul."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611'
original=area/'evidence/current-qm31-arithmetic-20261015/extraction/attempt-a/input/src/field.rs'
# Select the multiplication in impl QM31, not PreparedQm31Multiplier::mul.
def select(raw):
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();impl,*_=cut.find_item(Path(f.name),'impl QM31 {')
 with tempfile.NamedTemporaryFile() as f:
  f.write(impl);f.flush();item,*_=cut.find_item(Path(f.name),'pub fn mul(self, rhs: QM31)');return item
ref=select(original.read_bytes());pins=[]
for revision in [candidate+'^',candidate]:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-core/src/field.rs']);part=select(raw);assert part==ref
 pins.append(dict(revision=revision,mul_body_sha256=sha(part)))
external='''import AspisR1RhoPowerTail.Types
import ExtractedCurrentQM31Mul
open Aeneas Aeneas.Std Result
namespace AspisR1RhoPowerTail
abbrev Current := AspisR1Qm31ArithmeticProbe.field.QM31
def toCurrent (x : aspis_core.field.QM31) : Current :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}
def fromCurrent (x : Current) : aspis_core.field.QM31 :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}
-- Exact existing source function with coordinate-only carrier transport.
def aspis_core.field.QM31.mul (x y : aspis_core.field.QM31) :
    Result aspis_core.field.QM31 := do
  let out ← AspisR1Qm31ArithmeticProbe.field.QM31.mul (toCurrent x) (toCurrent y)
  pure (fromCurrent out)
end AspisR1RhoPowerTail
'''.encode()
outputs={n:(here/'rho-power-tail-generated'/n).read_bytes() for n in ['Types.lean','Funs.lean']};outputs['FunsExternal.lean']=external
# The attribute's anonymous instance uses a global short name and collides
# when the exact heap helper imports the original PublicPreparation enum.
# Expand only this registration with the same reader and a unique instance name.
variant=b"""@[discriminant isize]
inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant
"""
registration=b"""
-- Same ordinal reader; only the instance registration name is qualified.
def transport.Variant.read_discriminant (x : transport.Variant) : Isize :=
  match x with
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize
instance _root_.AspisR1RhoPowerTail.transport.Variant.instDiscriminant :
    Aeneas.Std.Discriminant transport.Variant Isize where
  read_discriminant := transport.Variant.read_discriminant
"""
assert outputs['Types.lean'].count(variant)==1
outputs['Types.lean']=outputs['Types.lean'].replace(variant,variant.replace(b'@[discriminant isize]\n',b'')+registration)

for n,b in outputs.items():
 p=area/'lean/AspisR1RhoPowerTail'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(source_mul_identity=pins,original_input=dict(path=str(original.relative_to(repo)),sha256=sha(original.read_bytes()),mul_body_sha256=sha(ref)),raw_generated={n:sha((here/'rho-power-tail-generated'/n).read_bytes()) for n in ['Types.lean','Funs.lean']},promoted={n:sha(b) for n,b in outputs.items()},discriminant_registration='Expand ordinal reader 0/1/2 exactly; qualify instance name to avoid original PublicPreparation global short-name collision. Original and corrected reader theorems audited separately.',scope='Raw carrier declarations and whole suffix unchanged. Only external QM31.mul binds to existing emitted byte-identical source operation with lossless coordinate transport. Original template is never imported. Source caller/prefix composition remains open.')
p=here/'rho-power-tail-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,generated_function_bodies_unchanged=True,ordinal_registration_only=True,mul_source_identical=True)))
