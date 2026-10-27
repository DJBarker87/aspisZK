import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee002
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve` (callee `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) :
  ∃ next, aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) =
    (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
      self statement_digest mask_nonce >>= next) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee002
