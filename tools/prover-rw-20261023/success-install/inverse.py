"""Retained generic inverses rebound to already selected release arithmetic."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/100bit-spend-path-20261013/evidence/prover-commit54-20261023/extraction/generic-owner/AspisR1Generic54/Funs.lean';s=p.read_text();names=['field.M31.pow_loop.body','field.M31.pow_loop','field.M31.pow','field.QM31.neg','field.M31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv','field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv','field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.try_inv'];blocks=[];pins={}
for n in names:
 m=re.search(r'^def\s+'+re.escape(n)+r'(?=\s|\{)',s,re.M);assert m,n
 b=s[m.start():s.index('\n/--',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest()
 b=b.replace('core.option.Option.Insts.','ProverRwDictionaryOptionSource.core.option.Option.Insts.')
 # This source's old backend spelled the nonnegative shift operand as i32.
 b=b.replace('wrapping_shr exp 1#i32','wrapping_shr exp 1#u32')
 blocks.append(b)
head='''import R1Z.ProverRwSuccessBorrow
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessInverseSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull ProverRwDictionaryTower
abbrev field.M31 := U32
abbrev field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev field.P := AspisR1ProducerRelease47.field.P
abbrev field.M31.ZERO := AspisR1ProducerRelease47.field.M31.ZERO
abbrev field.M31.ONE := AspisR1ProducerRelease47.field.M31.ONE
abbrev field.M31.mul := AspisR1ProducerRelease47.field.M31.mul
abbrev field.M31.add := AspisR1ProducerRelease47.field.M31.add
abbrev field.M31.neg := AspisR1ProducerRelease47.field.M31.neg
abbrev field.M31.Insts.CoreCmpPartialEqM31.eq := ProverRwDictionaryDerived.mEq
abbrev field.CM31.new := ProverRwDictionaryBytes.Src.complex

def field.CM31.mul (a b : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b))
def field.CM31.sub (a b : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.sub (toC a) (toC b))
def field.CM31.neg (a : C) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.neg (toC a))
'''
t=head+'\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessInverseSource\n'
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessInverseSource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-install/inverse-source.json').write_text(json.dumps(dict(path=str(p.relative_to(r)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),rewrites='Generic retained inverse/power control; arithmetic references rebound to release field methods with structural maps; old-backend nonnegative shift literal nominal i32-to-u32 port. Not the specialized addition-chain inv, nor square-based QM31 inherent inverse.'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
