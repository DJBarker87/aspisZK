import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_ReserveFallible
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_DurableReserve
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  P (Bool ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, self1) ← PV_W_R_ReserveFallible.program
    self statement_digest mask_nonce
  match r with
  | core.result.Result.Ok reserved =>
    pure (reserved, self1)
  | core.result.Result.Err error =>
    let ek ← perform (.base (.errorKind error))
    pure (false, { self1 with last_error := (some ek) })

theorem erase_program (ops : ExternalFuns)
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  erase ops (program self statement_digest mask_nonce) =
    @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve _ ops self statement_digest mask_nonce := by
  unfold program aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    rw [PV_W_R_ReserveFallible.erase_program]
  · rintro ⟨r, self1⟩
    try dsimp only
    cases r with
    | Ok reserved =>
      rfl
    | Err error =>
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_perform ops _
      · intro ek
        rfl

#print axioms erase_program

def store : Store aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore := ⟨program⟩

theorem store_source (ops : ExternalFuns) :
    sourceStore ops store = @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ ops := by
  apply congrArg aspis_prover.state_only_hiding.StateOnlyMaskNonceStore.mk
  funext self a b
  exact erase_program ops self a b

#print axioms store_source
end R1Z.PV_W_R_DurableReserve
