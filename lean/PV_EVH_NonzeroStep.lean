import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroStep
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where

structure Compatible (c : Callees) : Prop where

open ControlFlow

def run
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) (c : Callees) : P (ControlFlow (Std.U8 × Std.Usize) Std.U8) := do
  if i < 32#usize then
    let i1 ← PV_EVH_Prefix.lift (Array.index_usize bytes i)
    let combined1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (combined ||| i1))
    let i2 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize))
    pure (cont (combined1, i2))
  else
    pure (done combined)

theorem run_fixed
  (bytes : Array Std.U8 32#usize) (combined : Std.U8) (i : Std.Usize) (c : Callees) (compatible : Compatible c) :
    FinishedView (run bytes combined i c) (aspis_prover.state_only_entropy.entropy_nonzero32_loop.body bytes combined i) := by
  unfold run aspis_prover.state_only_entropy.entropy_nonzero32_loop.body
  by_cases condition : i < 32#usize
  · simp only [condition,if_true]
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro i1
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro combined1
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact PV_EVH_Prefix.lift_fixed _
        · intro i2
          exact PV_EVH_Prefix.lift_fixed _
  · simp only [condition,Bool.false_eq_true,if_false]
    exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_NonzeroStep
