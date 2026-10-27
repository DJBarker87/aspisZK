import R1Z.PV_OptB_ReservationFailure
set_option autoImplicit false
namespace R1Z.PV_OptB_ReservationBackend
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_OptB_ReservationFailure
variable [ExternalTypes] [ExternalFuns]

theorem failed {S : Type}
    (ledger : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (context : Context)
    (binding : Array U8 32#usize) (secret : Secret) (store : S) (e : Aeneas.Std.Error)
    (returned : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      ledger secret hash binding context store = .fail e) :
    prover.prove_masked_with_attempt ledger pub compiled .S2 hash context binding secret store = .fail e := by
  rw [prover.prove_masked_with_attempt,returned]
  rfl

theorem diverged {S : Type}
    (ledger : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (context : Context)
    (binding : Array U8 32#usize) (secret : Secret) (store : S)
    (returned : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      ledger secret hash binding context store = .div) :
    prover.prove_masked_with_attempt ledger pub compiled .S2 hash context binding secret store = .div := by
  rw [prover.prove_masked_with_attempt,returned]
  rfl

#print axioms failed
#print axioms diverged
end R1Z.PV_OptB_ReservationBackend
