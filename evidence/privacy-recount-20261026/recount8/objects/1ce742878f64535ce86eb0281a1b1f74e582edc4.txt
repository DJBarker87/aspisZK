import R1Z.ProverRwOuterEncode
import R1Z.ProverRwQueryRetry
set_option autoImplicit false
namespace R1Z.ProverRwOuterInstalled
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 ProverRwOuterContext
variable [ExternalTypes]

theorem prefix_entries (ops : ExternalFuns) (digest nonce : Array U8 32#usize) (c : Context) :
    letI : ExternalFuns := ProverRwCallerBinding.install (install ops)
    aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 digest nonce =
      construct digest nonce ∧
    aspis_core.state_only_hiding.StateOnlyHidingContext.encode c = encode c := by
  constructor <;> rfl

theorem caller_eight (ops : ExternalFuns) {C : Type} (entropy : Entropy C)
    (pub : Pub) (compiled : Compiled) (h : Hash) (store : Store) (callback : C) :
    letI : ExternalFuns := ProverRwCallerBinding.install (install ops)
    mapR sourceOutput (prover.prove_masked_retrying_with entropy pub compiled .S2 h store callback) =
      mapR drop (ProverCommitRetry34.eight
        (ProverRwQueryRetry.queryAttempt entropy pub compiled .S2 h) (callback,store)) := by
  exact ProverRwQueryRetry.admitted_eight (install ops) entropy pub compiled h store callback

#print axioms prefix_entries
#print axioms caller_eight
end R1Z.ProverRwOuterInstalled
