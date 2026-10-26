from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026'
s=(e/'sampler-array-Funs.lean.txt').read_text();a=s.index('/-- [aspis_core::field::P]');b=s.index('\nend PV_RW_SamplerArrayNative',a);body=s[a:b]
out='''import R1Z.PV_OrdinaryDivBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_SamplerArraySource
open Aeneas Aeneas.Std Result ControlFlow Error
'''+body+'''

def iterator_body (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    Result (ControlFlow ((Array U32 8#usize) × U64 × Usize) ((Array U32 8#usize) × U64)) := do
  if j > 0#usize then
    let next ← sampler_step.array_limb rank remainder j
    ok (cont next)
  else ok (done (rank,remainder))

theorem body (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    iterator_body rank remainder j =
      PV_OrdinarySource.sampler_owned.qm31_div_pass_loop.body rank remainder j := by
  unfold iterator_body PV_OrdinarySource.sampler_owned.qm31_div_pass_loop.body
  split
  · simp only [sampler_step.array_limb,aspis_core.field.P,
      PV_OrdinarySource.aspis_core.field.P,bind_assoc_eq,bind_tc_ok]
  · rfl

def iterator_loop (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    Result ((Array U32 8#usize) × U64) :=
  loop (fun (rank,remainder,j) => iterator_body rank remainder j) (rank,remainder,j)

theorem loop_reference (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    iterator_loop rank remainder j =
      PV_OrdinarySource.sampler_owned.qm31_div_pass_loop rank remainder j := by
  unfold iterator_loop PV_OrdinarySource.sampler_owned.qm31_div_pass_loop
  have same : (fun (rank,remainder,j) => iterator_body rank remainder j) =
      (fun (rank,remainder,j) => PV_OrdinarySource.sampler_owned.qm31_div_pass_loop.body rank remainder j) := by
    funext ⟨rank,remainder,j⟩
    exact body rank remainder j
  rw [same]

def pass (rank : Array U32 8#usize) : Result ((Array U32 8#usize) × U32) := do
  let (quotient,remainder) ← iterator_loop rank 0#u64 8#usize
  ok (quotient,UScalar.cast .U32 remainder)

theorem pass_reference (rank : Array U32 8#usize) :
    pass rank = PV_OrdinarySource.sampler_owned.qm31_div_pass rank := by
  unfold pass PV_OrdinarySource.sampler_owned.qm31_div_pass
  rw [loop_reference]
  rfl
#print axioms body
#print axioms loop_reference
#print axioms pass_reference
end R1Z.PV_RW_SamplerArraySource
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_SamplerArraySource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(e/'sampler-array-emission-map.json').write_text(json.dumps(dict(emitted_sha256=hashlib.sha256(s.encode()).hexdigest(),lean_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Literal emitted constants and array-state step unchanged. Import/namespace/boilerplate replaced. Added iterator control and equivalence theorems. No primitive stubs or new axioms.'),indent=2)+'\n')
