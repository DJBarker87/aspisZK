import R1Z.PV_RE_ClientStore1003
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientStore1003Outcomes
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
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
      (ProverRwOuterEncode.value (ProverRwOuterContextModel.context digest secret.mask_nonce))) = .ok binding) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} secret.mask_nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written)) (e : Error) (stopped : std.fs.OpenOptions.create_new written.1 true = .fail e),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .fail e := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro path h0 options h1 written h2 e stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientStore1003.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash path h0 options h1 written h2
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
    ∀ (path : std.path.PathBuf) (h0 : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path {store with last_error := none} secret.mask_nonce = .ok (path))
    (options : std.fs.OpenOptions) (h1 : std.fs.OpenOptions.new = .ok (options))
    (written : std.fs.OpenOptions × (std.fs.OpenOptions → std.fs.OpenOptions)) (h2 : std.fs.OpenOptions.write options true = .ok (written)) (stopped : std.fs.OpenOptions.create_new written.1 true = .div),
    @RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state = .div := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro path h0 options h1 written h2 stopped
  obtain ⟨next,hn⟩ := PV_RE_ClientStore1003.entered ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest binding serialization first_hash second_hash path h0 options h1 written h2
  rw [stopped] at hn
  exact hn
#print axioms divergence
end R1Z.PV_RE_ClientStore1003Outcomes
