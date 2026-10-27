import R1Z.PV_RE_ClientReserve7
import R1Z.ProverRwOuterMapErr
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ReserveGuards9
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]

/-- The source-selected outer dictionary discharges map_err, context, tag,
encoding, and all three reserve guards. The entropy, serialization, and hash
prefixes remain explicit; no successful whole-client result is assumed. -/
theorem client_to_store {C : Type} (ops : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : (ProverRwOuterMapErr.selected ops).op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper (ProverRwOuterMapErr.selected ops) entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize)
    (serialization : (ProverRwOuterMapErr.selected ops).op226 pub = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (second_hash : hash (bindingFrame bytes 2#u8
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C
      entropy pub compiled hash store state =
      (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        _ (ProverRwOuterMapErr.selected ops) store digest secret.mask_nonce >>= next) := by
  let D := ProverRwOuterMapErr.selected ops
  let context := ProverRwOuterContextModel.context digest secret.mask_nonce
  have hm : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes) := rfl
  have hc : D.op115 digest secret.mask_nonce = .ok context :=
    ProverRwOuterContext.construct_fields digest secret.mask_nonce
  have ht : D.op234 .S2 = .ok 2#u8 := rfl
  have he : D.op116 context = .ok (ProverRwOuterEncode.value context) :=
    ProverRwOuterEncode.encode_total context
  obtain ⟨next,hn⟩ := PV_RE_ClientReserve7.client_to_reserve D entropy pub compiled hash store
    state state1 secret guard entropy_prefix bytes digest serialization hm first_hash context hc
    2#u8 ht (ProverRwOuterEncode.value context) he binding second_hash
  have checks := ProverRwOuterGuardBridge.checked
    {ops with op12 := @ProverRwOuterMapErr.map_err}
    (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ D)
    secret hash binding digest store
  rw [checks] at hn
  unfold ProverRwOuterAfterChecks.afterChecks at hn
  rw [PV_RE_ClientEntry.bind_assoc] at hn
  exact ⟨_,hn⟩

#print axioms client_to_store
end R1Z.PV_RE_ReserveGuards9
