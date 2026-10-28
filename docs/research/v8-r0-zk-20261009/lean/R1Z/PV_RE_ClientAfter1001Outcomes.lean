import R1Z.PV_RE_ClientAfter1001
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientAfter1001Outcomes
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
open PV_RE_AfterPrefix1001 (Z Pre Material)
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
    ∀ (store1 : Store) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce = .ok (true,store1)) (e : Error) (stopped : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .fail e),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .fail e := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro store1 h0 e stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientAfter1001.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash store1 h0
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
    ∀ (store1 : Store) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce = .ok (true,store1)) (stopped : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .div),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .div := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro store1 h0 stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientAfter1001.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash store1 h0
  rw [stopped] at hn
  exact hn
#print axioms divergence
end R1Z.PV_RE_ClientAfter1001Outcomes
