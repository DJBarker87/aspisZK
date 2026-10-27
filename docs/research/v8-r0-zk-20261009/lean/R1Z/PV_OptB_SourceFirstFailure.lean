import R1Z.ProverRwEffectCallback
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_SourceFirstFailure
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Full extracted caller, any first callback Entropy error. No proof body,
compiled trace, hash, or witness is inspected after this boundary. This is
only the first-callback case, not a theorem about later reached failures. -/
theorem first_callback_error {S : Type}
    (account : ProverRwEffectCallback.Account S) (state next : S)
    (called :
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account).call_mut state 0#usize =
        .ok (.Err .Entropy,next))
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (store : Store) :
    RealR1_client.prove_for_proof_accounts account pub compiled hash store state =
      .ok (.Err .Entropy,store) := by
  have raw := called
  dsimp only [RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError] at raw
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
  rw [variant]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [prover.retry_attempt]
  simp only [prover.ATTEMPT_CAP,show ¬ (0#usize : Usize) >= 8#usize from by decide,
    if_false,raw,bind_tc_ok,Aeneas.Std.uncurry]
  rfl

/-- Every observer of the complete returned source result agrees on this
fixed public first-callback failure, even when private compiled inputs and
body hash inputs differ. No decision bit or side channel is projected away. -/
theorem first_callback_observation {S W Observation : Type}
    (account : ProverRwEffectCallback.Account S) (state next : S)
    (called :
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account).call_mut state 0#usize =
        .ok (.Err .Entropy,next))
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (pub : Pub) (compiled : W → Compiled) (hash : W → Hash) (store : Store)
    (observe : Result (core.result.Result prover.RetriedProof verifier.Error × Store) → Observation)
    (w u : W) :
    observe (RealR1_client.prove_for_proof_accounts account pub (compiled w) (hash w) store state) =
      observe (RealR1_client.prove_for_proof_accounts account pub (compiled u) (hash u) store state) := by
  rw [first_callback_error account state next called variant,
      first_callback_error account state next called variant]

#print axioms first_callback_error
#print axioms first_callback_observation
end R1Z.PV_OptB_SourceFirstFailure
