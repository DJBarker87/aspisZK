import R1Z.PV_RunJoin_SelectedOsFailure
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedErrorPrelude
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel ProverRwEffectSource
theorem source_prelude_error (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    {S W : Type} (account : ProverRwEffectCallback.Account S) (state next : S)
    (nonce : Array U8 32#usize)
    (called : account.call_mut state 0#usize = .ok (nonce,next))
    (entered : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok true) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    letI : ExternalFuns := PV_RunJoin_ZeroizingPrefix.selected base ops
    ∃ input back, before = .ok (input,back) ∧
    ∀ (err : getrandom.error.Error) (written : Slice U8),
    getrandom.fill input = .ok (.Err err,written) →
    ∀ (pub : W → Pub) (compiled : W → Compiled) (hash : W → Hash)
      (store : Store) (w u : W),
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      .ok (.Err .Entropy,store) ∧
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      RealR1_client.prove_for_proof_accounts account (pub u) (compiled u) (hash u) store state := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  letI : ExternalFuns := PV_RunJoin_ZeroizingPrefix.selected base ops
  obtain ⟨input,back,hprefix⟩ := PV_RunJoin_ZeroizingBefore.before_returns base ops
  refine ⟨input,back,hprefix,?_⟩
  exact PV_RunJoin_SelectedOsFailure.selected_error base ops account state next nonce called entered input back hprefix

#print axioms source_prelude_error
end R1Z.PV_RunJoin_SelectedErrorPrelude
