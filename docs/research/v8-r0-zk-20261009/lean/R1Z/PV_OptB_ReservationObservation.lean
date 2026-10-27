import R1Z.PV_OptB_ReservationFailure
set_option autoImplicit false
namespace R1Z.PV_OptB_ReservationObservation
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_OptB_ReservationFailure
variable [ExternalTypes] [ExternalFuns]

/-- Complete source-result observation on the fixed failed reservation prefix.
The theorem does not assert witness-independent entry into later prefixes. -/
theorem prefix_observation {S : Type}
    (ledger : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (context : Context)
    (binding : Array U8 32#usize) (secret : Secret) (store after : S)
    (raw : MaskError) (e : verifier.Error)
    (returned : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      ledger secret hash binding context store = .ok (.Err raw,after))
    (mapped : core.result.Result.map_err (T := Material) (BuiltinFnOnce MaskError verifier.Error)
      (.Err raw) prover.mask_error = .ok (.Err e)) (other : Compiled) {Observation : Type}
    (observe : Result (core.result.Result Proof verifier.Error × S) → Observation) :
    observe (prover.prove_masked_with_attempt ledger pub compiled .S2 hash context binding secret store) =
      observe (prover.prove_masked_with_attempt ledger pub other .S2 hash context binding secret store) := by
  rw [PV_OptB_ReservationFailure.prefix_error ledger pub compiled hash context binding secret store after raw e returned mapped,
    PV_OptB_ReservationFailure.prefix_error ledger pub other hash context binding secret store after raw e returned mapped]

#print axioms prefix_observation
end R1Z.PV_OptB_ReservationObservation
