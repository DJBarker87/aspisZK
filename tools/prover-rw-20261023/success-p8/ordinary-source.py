"""Literal owned sampler source; nominal carriers and current extracted ctor only."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8'
s=(e/'ordinary-owned-Funs.lean.txt').read_text();a=s.index('/-- [aspis_core::field::P]');b=s.index('\nend PV_OrdinaryOwned',a)
assert all('def sampler_owned.'+n in s for n in ['qm31_div_pass','low_base_p_digits','decode8','ordinary_sample'])
out='''import R1Z.ProverRwSuccessNativeNormalize
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OrdinarySource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.WideExact.new := ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.new
'''+s[a:b]+'''
theorem ordinary_unfold (block : Array U8 32#usize) :
    sampler_owned.ordinary_sample block = (do
      let (digits,_) ← sampler_owned.low_base_p_digits block
      sampler_owned.decode8 digits) := rfl
theorem bytes_done (block : Array U8 32#usize) (rank : Array U32 8#usize)
    (i : Usize) (h : ¬ i < 8#usize) :
    sampler_owned.low_base_p_digits_loop0.body block rank i = ok (done rank) := by
  simp only [sampler_owned.low_base_p_digits_loop0.body,h,if_false]
theorem digits_done (rank digits : Array U32 8#usize) (i : Usize) (h : ¬ i < 8#usize) :
    sampler_owned.low_base_p_digits_loop1.body rank digits i = ok (done (rank,digits)) := by
  simp only [sampler_owned.low_base_p_digits_loop1.body,h,if_false]
#print axioms digits_done
#print axioms bytes_done
#print axioms ordinary_unfold
end R1Z.PV_OrdinarySource
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OrdinarySource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 (e/'ordinary-source-map.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Literal emitted constant/control/read/decoder bodies. Structural Full carrier aliases; only opaque WideExact.new bound to the already extracted current constructor. Generated options/import boilerplate omitted; standalone unfolding theorem added. Native shipped/reference equality remains OPEN.'),indent=2)+'\n')
