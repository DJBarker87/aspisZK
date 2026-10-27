import R1Z.PV_RE_AfterPrefix1000
import R1Z.PV_RE_AfterChecks10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientAfter1000
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
open PV_RE_AfterPrefix1000
theorem prefix {C : Type} (ops : ExternalFuns)
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
    ∃ next, @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store (ProverRwOuterContextModel.context digest secret.mask_nonce).statement_digest (ProverRwOuterContextModel.context digest secret.mask_nonce).mask_nonce >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  apply PV_RE_BindTransport10.compose _ _ _
    (PV_RE_AfterChecks10.client_to_afterChecks ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash)
  exact PV_RE_AfterPrefix1000.prefix aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore secret hash binding (ProverRwOuterContextModel.context digest secret.mask_nonce) store 
#print axioms prefix
end R1Z.PV_RE_ClientAfter1000
