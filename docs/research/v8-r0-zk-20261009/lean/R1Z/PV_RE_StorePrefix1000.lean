import R1Z.PV_RE_BindTransportB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_StorePrefix1000
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
/-- Actual ordered reservation prefix 0: all earlier native successes are explicit. -/
theorem entered (store : Store) (statement nonce : Array U8 32#usize) :
    ∃ next, aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible store statement nonce =
      (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} nonce >>= next) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_StorePrefix1000
