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
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoPowerTail'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(source_mul_identity=pins,original_input=dict(path=str(original.relative_to(repo)),sha256=sha(original.read_bytes()),mul_body_sha256=sha(ref)),raw_generated={n:sha((here/'rho-power-tail-generated'/n).read_bytes()) for n in ['Types.lean','Funs.lean']},promoted={n:sha(b) for n,b in outputs.items()},scope='Raw carriers and whole suffix unchanged. Only external QM31.mul binds to existing emitted byte-identical source operation with lossless coordinate transport. Original template is never imported. Source caller/prefix composition remains open.')
p=here/'rho-power-tail-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,raw_source_unchanged=True,mul_source_identical=True)))
