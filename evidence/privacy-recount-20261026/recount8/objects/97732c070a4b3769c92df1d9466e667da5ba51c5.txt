import R1Z.PV_RunJoin_ZeroizingBefore
import R1Z.PV_RunJoin_VariantIdentity
import R1Z.PV_RunJoin_DictionaryIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedOsFailure
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel ProverRwEffectSource

theorem selected_error (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    {S W : Type} (account : ProverRwEffectCallback.Account S) (state next : S)
    (nonce : Array U8 32#usize)
    (called : account.call_mut state 0#usize = .ok (nonce,next))
    (entered : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok true) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    letI : ExternalFuns := PV_RunJoin_ZeroizingPrefix.selected base ops
    ∀ input back, before = .ok (input,back) →
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
  intro input back hprefix err written fault pub compiled hash store w u
  have mapped := PV_RunJoin_OsFailurePure.client_map_error
    (PV_RunJoin_ZeroizingPrefix.selected base ops)
    (PV_RunJoin_DictionaryIdentity.map_error base ops) account err
  have variant := PV_RunJoin_OsFailurePure.s2_ne
    (PV_RunJoin_ZeroizingPrefix.selected base ops)
    (PV_RunJoin_VariantIdentity.selected_variant base ops)
  exact PV_RunJoin_SourceFailureIndependence.source_witness_independent account state next nonce
    called entered input back hprefix err written fault mapped variant pub compiled hash store w u

#print axioms selected_error
end R1Z.PV_RunJoin_SelectedOsFailure
