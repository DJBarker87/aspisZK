import R1Z.PV_RE_ClientAfter1002
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientAfter1002Outcomes
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
open PV_RE_AfterPrefix1002
theorem failure {C : Type} (ops : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (entropy_prefix : (EntropyWrapper (ProverRwOuterMapErr.selected ops) entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
    (bytes : alloc.vec.Vec U8) (digest binding : Array U8 32#usize)
    (serialization : (ProverRwOuterMapErr.selected ops).op226 pub = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)
    (second_hash : hash (bindingFrame bytes 2#u8
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (store1 : Store) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce = .ok (true,store1))
    (private_entropy : Array U8 32#usize) (h1 : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .ok private_entropy) (e : Error) (stopped : aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) private_entropy ({statement_digest := (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest,mask_nonce := (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce,consumed := false} : Pre) = .fail e),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .fail e := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro store1 h0 private_entropy h1 e stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientAfter1002.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash store1 h0 private_entropy h1
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
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (store1 : Store) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce = .ok (true,store1))
    (private_entropy : Array U8 32#usize) (h1 : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .ok private_entropy) (stopped : aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) private_entropy ({statement_digest := (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest,mask_nonce := (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce,consumed := false} : Pre) = .div),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .div := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro store1 h0 private_entropy h1 stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientAfter1002.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash store1 h0 private_entropy h1
  rw [stopped] at hn
  exact hn
#print axioms divergence
end R1Z.PV_RE_ClientAfter1002Outcomes
