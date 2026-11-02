import R1Z.PV_RunJoin_BoundaryFold73
import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundarySource73
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BoundaryFold73
attribute [local irreducible] ProverRwP6BoundaryStep.advance initial

def finish (s : ProverRwP6BoundaryStep.Acc) : Result Q := do
  let a ← ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 s.a
  let b ← ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 s.b
  let c0 ← ProverRwP6BoundarySource.aspis_core.field.CM31.new a b
  let c ← ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 s.c
  let d ← ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64 s.d
  let c1 ← ProverRwP6BoundarySource.aspis_core.field.CM31.new c d
  ok ⟨c0,c1⟩

theorem complete (p : Nat → Q) :
    ProverRwP6BoundarySource.boundary_flat (PV_RunJoin_MergeArray35.array p)=
      finish (fold p 27 1 (initial (p 0))) := by
  unfold ProverRwP6BoundarySource.boundary_flat
  rw [PV_RunJoin_MergeArray35.read p 0#usize (by decide)]
  simp only [lift,bind_tc_ok]
  have init : (⟨U64.wrapping_mul 2#u64 (core.convert.num.FromU64U32.from (p 0).c0.a),
      U64.wrapping_mul 2#u64 (core.convert.num.FromU64U32.from (p 0).c0.b),
      U64.wrapping_mul 2#u64 (core.convert.num.FromU64U32.from (p 0).c1.a),
      U64.wrapping_mul 2#u64 (core.convert.num.FromU64U32.from (p 0).c1.b)⟩ : ProverRwP6BoundaryStep.Acc)=initial (p 0) := by unfold initial;rfl
  rw [init]
  repeat' first
    | (rw [PV_RunJoin_MergeArray35.read p _ (by decide)];simp only [lift,bind_tc_ok])
    | (rw [ProverRwP6BoundaryStep.step];simp only [lift,bind_tc_ok])
  simp only [fold]
  rfl

#print axioms finish
#print axioms complete
end R1Z.PV_RunJoin_BoundarySource73
