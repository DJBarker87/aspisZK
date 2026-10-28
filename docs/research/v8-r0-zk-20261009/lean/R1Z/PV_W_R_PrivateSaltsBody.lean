import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_PrivateSaltStep
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PrivateSaltsBody
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) :
  P (ControlFlow ((core.result.Result (alloc.vec.Vec (Array Std.U8
    32#usize)) verifier.Error) × Std.Usize) (core.result.Result (alloc.vec.Vec
    (Array Std.U8 32#usize)) verifier.Error)) := do
  if index < count then
    PV_W_StructuredBinds.join (do
      match result with
      | core.result.Result.Ok salts =>
        let i ← invoke "Aeneas.Std.lift" (fun ops =>
            letI : ExternalFuns := ops
            let hash := sourceHash ops hash
            Aeneas.Std.lift (UScalar.cast .U32 index))
        PV_W_R_PrivateSaltStep.program reserved context hash tag i salts
      | core.result.Result.Err _ =>
        pure result) (fun result1 => do
      let index1 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          let hash := sourceHash ops hash
          Aeneas.Std.lift (Std.Usize.wrapping_add index 1#usize))
      pure (cont (result1, index1)))
  else
    pure (done result)

theorem erase_program (ops : ExternalFuns)
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Hash)
  (tag : Std.U8) (count : Std.Usize)
  (result : core.result.Result (alloc.vec.Vec (Array Std.U8 32#usize))
  verifier.Error) (index : Std.Usize) :
  erase ops (program reserved context hash tag count result index) =
    @prover.derive_private_salts_loop.body _ ops reserved context (sourceHash ops hash) tag count result index := by
  unfold program prover.derive_private_salts_loop.body
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    rw [PV_W_StructuredBinds.erase_join]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      try dsimp only
      cases result with
      | Ok salts =>
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro i
          rw [PV_W_R_PrivateSaltStep.erase_program]
      | Err unused1_0 =>
        rfl
    · intro result1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro index1
        rfl
  ·
    rfl

#print axioms erase_program
end R1Z.PV_W_R_PrivateSaltsBody
