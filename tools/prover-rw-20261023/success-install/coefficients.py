"""Retain the exact common S1/S2 row and coefficient generator bodies.
The D table remains with its existing callback and is not selected here.
"""
from pathlib import Path
import re,hashlib,sys,json
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/evidence/s3-s9-current-repin-20261020/variant-row-source-cut-v3/generated/AspisR1VariantRowSource/Funs.lean'
s=p.read_text();names=['transport.TAU','transport.Variant.row_loop.body','transport.Variant.row_loop','transport.Variant.row','transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut','transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT.call_once','transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeT','transport.Variant.coefficients.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT','transport.Variant.coefficients'];blocks=[];pins={}
for n in names:
 m=re.search(r'^def\s+'+re.escape(n)+r'(?=\s|\{)',s,re.M);assert m,n
 b=s[m.start():s.index('\n/--',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest()
 if n=='transport.Variant.row':
  a=b.index('  let b ←');e=b.index('    transport.Variant.row_loop',a)
  b=b[:a]+b[e:].replace('    transport.Variant.row_loop','  transport.Variant.row_loop',1)
 blocks.append(b)
t='''import R1Z.ProverRwSuccessWideSource
import R1Z.ProverRwSuccessArrayFromFn
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessCoefficientsSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev core.array.from_fn := @ProverRwSuccessArrayFromFn.fromFn
abbrev transport.Variant := ProverRwFull.transport.Variant
abbrev transport.Variant.coefficients.closure (T : Type) := Array T 1024#usize × transport.Variant
'''+ '\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessCoefficientsSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessCoefficientsSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume/coefficients-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),rewrite='Common S1/S2 row branch only; no D interpretation or table; old D callback retained by selector. New namespace and nominal closure/variant aliases only.'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
