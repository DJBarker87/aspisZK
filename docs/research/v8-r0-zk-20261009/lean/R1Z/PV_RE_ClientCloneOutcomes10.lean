import R1Z.PV_RE_ClientCloneB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientCloneOutcomes10
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
open PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7 PV_RE_MaskedClone10
variable [ExternalTypes]
theorem failure {C : Type} (ops : ExternalFuns)
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
      secret hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) store = .ok (.Ok (reserved,material),store1))
    (e : Error) (stopped : (ProverRwOuterMapErr.selected ops).op231 compiled.semantic_c1 = .fail e) :
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .fail e := by
  obtain ⟨next,hn⟩ := PV_RE_ClientCloneB10.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash store1 reserved material reservation
  rw [stopped] at hn
  exact hn
#print axioms failure
theorem divergence {C : Type} (ops : ExternalFuns)
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
      secret hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) store = .ok (.Ok (reserved,material),store1))
    (stopped : (ProverRwOuterMapErr.selected ops).op231 compiled.semantic_c1 = .div) :
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .div := by
  obtain ⟨next,hn⟩ := PV_RE_ClientCloneB10.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash store1 reserved material reservation
  rw [stopped] at hn
  exact hn
#print axioms divergence
end R1Z.PV_RE_ClientCloneOutcomes10
