import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_PreReservedReserve
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (self : aspis_prover.state_only_entropy.PreReservedNonce)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  P (Bool × aspis_prover.state_only_entropy.PreReservedNonce) := do
  if self.consumed then
    pure (false, self)
  else
    let b ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
        letI : ExternalFuns := ops
        core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        statement_digest self.statement_digest)
    if b then
      pure (false, self)
    else
      let b1 ← invoke "core.array.equality.PartialEqArray.ne" (fun ops =>
          letI : ExternalFuns := ops
          core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 mask_nonce
          self.mask_nonce)
      if b1 then
        pure (false, self)
      else
        pure (true, { self with consumed := true })

theorem erase_program (ops : ExternalFuns)
  (self : aspis_prover.state_only_entropy.PreReservedNonce)
  (statement_digest : Array Std.U8 32#usize)
  (mask_nonce : Array Std.U8 32#usize) :
  erase ops (program self statement_digest mask_nonce) =
    @aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve self statement_digest mask_nonce := by
  unfold program aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    rfl
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro b
      try dsimp only
      apply PV_W_Callbacks.erase_if_congr
      ·
        rfl
      ·
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro b1
          try dsimp only
          apply PV_W_Callbacks.erase_if_congr
          ·
            rfl
          ·
            rfl

#print axioms erase_program

def store : Store aspis_prover.state_only_entropy.PreReservedNonce := ⟨program⟩

theorem store_source (ops : ExternalFuns) :
    sourceStore ops store = @aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore := by
  apply congrArg aspis_prover.state_only_hiding.StateOnlyMaskNonceStore.mk
  funext self a b
  exact erase_program ops self a b

#print axioms store_source
end R1Z.PV_W_R_PreReservedReserve
