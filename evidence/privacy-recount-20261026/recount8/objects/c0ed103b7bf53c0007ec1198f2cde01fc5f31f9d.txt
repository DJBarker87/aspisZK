import R1Z.PV_RunJoin_SourceOsFailure
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceFailureIndependence
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel ProverRwEffectSource
variable [ExternalTypes] [ExternalFuns]

/-- Witness independence at the FULL extracted entry. Account callback state,
ledger and dictionary are fixed. Public/compiled/hash data may vary arbitrarily
with the witness: none is examined after the named first-draw fault. This is
not an assertion that an arbitrary native scheduler is independent of w. -/
theorem source_witness_independent {S W : Type}
    (account : ProverRwEffectCallback.Account S) (state next : S)
    (nonce : Array U8 32#usize)
    (called : account.call_mut state 0#usize = .ok (nonce,next))
    (entered : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok true)
    (input : Slice U8) (back : Back) (hprefix : before = .ok (input,back))
    (err : getrandom.error.Error) (written : Slice U8)
    (fault : getrandom.fill input = .ok (.Err err,written))
    (mapped : core.result.Result.map_err
      (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError account)
      (.Err (.Os err) : Status) () = .ok (.Err .Entropy))
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (pub : W → Pub) (compiled : W → Compiled) (hash : W → Hash)
    (store : Store) (w u : W) :
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      .ok (.Err .Entropy,store) ∧
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      RealR1_client.prove_for_proof_accounts account (pub u) (compiled u) (hash u) store state := by
  have factory := PV_RunJoin_SourceOsFailure.factory_os_error nonce entered input back hprefix err written fault
  have left := PV_RunJoin_SourceOsFailure.client_on_factory_error account state next nonce called err factory
    mapped variant (pub w) (compiled w) (hash w) store
  have right := PV_RunJoin_SourceOsFailure.client_on_factory_error account state next nonce called err factory
    mapped variant (pub u) (compiled u) (hash u) store
  exact ⟨left,left.trans right.symm⟩

#print axioms source_witness_independent
end R1Z.PV_RunJoin_SourceFailureIndependence
