import R1Z.PV_RE_AttemptReserve7
import R1Z.PV_RE_ClientBindingHash7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientReserve7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
theorem client_to_reserve {C : Type} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)
    (tag : U8) (tag_prefix : D.op234 .S2 = .ok tag)
    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded)
    (binding : Array U8 32#usize)
    (second_hash : hash (bindingFrame bytes tag encoded) = .ok binding) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      (@aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        _ D Store
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        secret hash binding context store >>= next) := by
  apply PV_RE_ClientAttempt7.lift_prefix D entropy pub compiled hash store state state1 secret guard entropy_prefix (@aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        _ D Store
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        secret hash binding context store)
  exact PV_RE_AttemptReserve7.attempt_to_reserve D pub compiled .S2 hash secret store bytes digest serialization map_error first_hash context context_prefix tag tag_prefix encoded encode_prefix binding second_hash
#print axioms client_to_reserve
end R1Z.PV_RE_ClientReserve7
