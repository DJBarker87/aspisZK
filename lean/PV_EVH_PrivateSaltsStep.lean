import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrivateSaltsStep
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  derive_private_salt_step_OPEN : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)), P ((core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
    verifier.Error))

structure Compatible (c : Callees) : Prop where
  derive_private_salt_step_fixed : ∀ (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (index : Std.U32)
  (salts : alloc.vec.Vec (Array Std.U8 32#usize)), FinishedView (c.derive_private_salt_step_OPEN reserved context hash tag index salts) (prover.derive_private_salt_step reserved context hash tag index salts)

open ControlFlow

def run
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) (c : Callees) : P (ControlFlow ((core.result.Result (alloc.vec.Vec (Array Std.U8
    32#usize)) verifier.Error) × Std.Usize) (core.result.Result (alloc.vec.Vec
    (Array Std.U8 32#usize)) verifier.Error)) := do
  if index < count then
    let result1 ← match result with
      | core.result.Result.Ok salts =>
        let i ← PV_EVH_Prefix.lift (Aeneas.Std.lift (UScalar.cast .U32 index))
        c.derive_private_salt_step_OPEN reserved context hash tag i salts
      | core.result.Result.Err _ =>
        pure result
    let index1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add index 1#usize))
    pure (cont (result1, index1))
  else
    pure (done result)

theorem run_fixed
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) (c : Callees) (compatible : Compatible c) :
    FinishedView (run reserved context hash tag count result index c) (prover.derive_private_salts_loop.body reserved context hash tag count result index) := by
  unfold run prover.derive_private_salts_loop.body
  by_cases condition : index < count
  · simp only [condition,if_true]
    try dsimp only
    cases result with
    | Ok salts =>
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro i
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact compatible.derive_private_salt_step_fixed _ _ _ _ _ _
        · intro result1
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro index1
            exact PV_EVH_Prefix.lift_fixed _
    | Err unused1 =>
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro index1
        exact PV_EVH_Prefix.lift_fixed _
  · simp only [condition,if_false]
    exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_PrivateSaltsStep
