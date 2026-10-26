import R1Z.PV_OrdinaryDivBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_SamplerArraySource
open Aeneas Aeneas.Std Result ControlFlow Error
/-- [aspis_core::field::P]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [pv_rw_step::sampler_step::array_limb]:
    Source: 'sampler_step.rs', lines 39:0-45:1
    Visibility: public -/
def sampler_step.array_limb
  (rank : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result ((Array Std.U32 8#usize) × Std.U64 × Std.Usize)
  := do
  let j1 ← lift (Std.Usize.wrapping_sub j 1#usize)
  let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
  let i1 ← Array.index_usize rank j1
  let i2 ← lift (core.convert.num.FromU64U32.from i1)
  let dividend ← lift (i ||| i2)
  let i3 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i4 ← dividend / i3
  let i5 ← lift (UScalar.cast .U32 i4)
  let rank1 ← Array.update rank j1 i5
  let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let remainder1 ← dividend % i6
  ok (rank1, remainder1, j1)


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
