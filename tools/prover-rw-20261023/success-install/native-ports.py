"""Literal current native wide/CT bodies, with explicit retained leaf bindings."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next';p=e/'ports-generated-002/Funs.lean';s=p.read_text();blocks=[];pins={}
for m in re.finditer(r'^def\s+([\w.]+)(?=\s|\{)',s,re.M):
 n=m[1];end=s.find('\n/--',m.end());assert end>=0 or n=='wide_inv'
 b=s[m.start():end if end>=0 else s.index('\nend ProverRwSuccessPorts',m.end())].strip();pins[n]=hashlib.sha256(b.encode()).hexdigest()
 if n=='aspis_core.field.ct.reduce64':
  assert b.count('31#i32')==2
  b=b.replace('31#i32','31#u32') # Existing Aeneas port's shift-count carrier; both literals are 31.
 b=b.replace('core.option.Option.Insts.','ProverRwDictionaryOptionSource.core.option.Option.Insts.')
 blocks.append(b)
head='''import R1Z.ProverRwSuccessErrorInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessNativePorts
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.canonical_qm31.closure := Unit
abbrev aspis_core.field.P : Result U32 := .ok AspisR1ProducerRelease47.field.P
abbrev aspis_core.field.M31.ZERO : Result U32 := .ok 0#u32
abbrev aspis_core.field.M31.ONE : Result U32 := .ok 1#u32
abbrev aspis_core.field.CM31.ZERO : Result aspis_core.field.CM31 := .ok ⟨0#u32,0#u32⟩
abbrev aspis_core.field.CM31.ONE : Result aspis_core.field.CM31 := .ok ⟨1#u32,0#u32⟩
abbrev aspis_core.field.M31.mul := AspisR1ProducerRelease47.field.M31.mul
abbrev aspis_core.field.M31.add := AspisR1ProducerRelease47.field.M31.add
abbrev aspis_core.field.M31.neg := AspisR1ProducerRelease47.field.M31.neg
abbrev aspis_core.field.M31.pow := ProverRwSuccessInverseSource.field.M31.pow
abbrev aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq := ProverRwDictionaryDerived.mEq
abbrev aspis_core.field.CM31.new := ProverRwDictionaryBytes.Src.complex
abbrev aspis_core.field.CM31.mul := ProverRwSuccessInverseSource.field.CM31.mul
abbrev aspis_core.field.CM31.sub := ProverRwSuccessInverseSource.field.CM31.sub
abbrev aspis_core.field.CM31.neg := ProverRwSuccessInverseSource.field.CM31.neg
abbrev aspis_core.field.QM31.mul := ProverRwDictionaryTower.qMul
abbrev aspis_core.field.QM31.sub := ProverRwDictionaryTower.qSub
abbrev aspis_core.field.QM31.neg := ProverRwSuccessInverseInstall.Src.qNeg
'''
t=head+'\n\n'.join(blocks)+'\nend R1Z.ProverRwSuccessNativePorts\n';o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessNativePorts.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t);(e/'native-ports-source.json').write_text(json.dumps(dict(source=str(p.relative_to(r)),sha256=hashlib.sha256(s.encode()).hexdigest(),declarations=pins,output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='Namespace, explicit nominal carrier aliases, retained primitive field/pow/option bindings; two literal shift counts 31 map I32 to the current Aeneas U32 shift-count carrier. Actual CT reducer/normalizer/generic inverses are retained, not substituted. Primitive native field adequacy remains inherited.'),indent=2)+'\n')
