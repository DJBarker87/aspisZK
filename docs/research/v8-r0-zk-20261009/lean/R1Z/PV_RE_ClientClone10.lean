import R1Z.PV_RE_MaskedClone10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientClone10
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
open PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7 PV_RE_MaskedClone10
variable [ExternalTypes]
theorem entered {C : Type} (ops : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (entropy_prefix : (EntropyWrapper (ProverRwOuterMapErr.selected ops) entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize)
    (serialization : (ProverRwOuterMapErr.selected ops).op226 pub = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (second_hash : hash (bindingFrame bytes 2#u8
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding)
    (store1 : Store) (reserved : Reserved) (material : Material)
    (reservation : @aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      _ (ProverRwOuterMapErr.selected ops) Store
      (@aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore _ (ProverRwOuterMapErr.selected ops))
      secret hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) store = .ok (.Ok (reserved,material),store1)) :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state =
      ((ProverRwOuterMapErr.selected ops).op231 compiled.semantic_c1 >>= next) := by
  let D := ProverRwOuterMapErr.selected ops
  letI : ExternalFuns := D
  let context := ProverRwOuterContextModel.context digest secret.mask_nonce
  have hm : D.op12 prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (.Ok bytes) () = .ok (.Ok bytes) := rfl
  have hc : D.op115 digest secret.mask_nonce = .ok context := ProverRwOuterContext.construct_fields digest secret.mask_nonce
  have ht : D.op234 .S2 = .ok 2#u8 := rfl
  have he : D.op116 context = .ok (ProverRwOuterEncode.value context) := ProverRwOuterEncode.encode_total context
  apply PV_RE_ClientAttempt7.lift_prefix D entropy pub compiled hash store state state1 secret (by rfl) entropy_prefix (D.op231 compiled.semantic_c1)
  unfold prover.prove_masked_attempt
  change ∃ next, (D.op226 pub >>= _) = _
  rw [serialization]
  change ∃ next, (D.op12 prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (.Ok bytes) () >>= _) = _
  rw [hm]
  change ∃ next, (hash (publicFrame bytes) >>= _) = _
  rw [first_hash]
  change ∃ next, (D.op115 digest secret.mask_nonce >>= _) = _
  rw [hc]
  change ∃ next, (D.op234 .S2 >>= _) = _
  rw [ht]
  change ∃ next, (D.op116 context >>= _) = _
  rw [he]
  change ∃ next, (hash (bindingFrame bytes 2#u8 (ProverRwOuterEncode.value context)) >>= _) = _
  rw [second_hash]
  unfold prover.prove_masked_with_attempt
  rw [reservation]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_ClientClone10
