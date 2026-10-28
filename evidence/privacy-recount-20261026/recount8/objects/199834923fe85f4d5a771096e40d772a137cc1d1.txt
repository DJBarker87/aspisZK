import R1Z.ProverRwEffectRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceOsFailure
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape ProverRwEffectOwner
open ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- The full frozen factory, not the Draw64 prototype. Its dictionary is
unchanged: the prefix and kernel-return facts are named hypotheses. -/
theorem factory_os_error (nonce : Array U8 32#usize)
    (entered : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok true)
    (input : Slice U8) (back : Back) (hprefix : before = .ok (input,back))
    (err : getrandom.error.Error) (written : Slice U8)
    (fault : getrandom.fill input = .ok (.Err err,written)) :
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
      .ok (.Err (.Os err)) := by
  rw [← pure_owner_eq]
  unfold pureOwner
  rw [entered]
  simp only [bind_tc_ok,if_true]
  rw [loop]
  simp only [aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT,emit,
    show (0#usize : Usize) < 16#usize from by decide,if_true,hprefix,ProverRwEffectTape.pure,
    fault,bind_tc_ok,ProverRwEffectControl.after_os_error]

/-- Source entry stops before prove_masked_attempt for arbitrary public,+compiled and hash inputs. No replacement sampler or variant dictionary is
installed here. -/
theorem client_on_factory_error {S : Type} (account : ProverRwEffectCallback.Account S)
    (state next : S) (nonce : Array U8 32#usize)
    (called : account.call_mut state 0#usize = .ok (nonce,next))
    (err : getrandom.error.Error)
    (factory : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
      .ok (.Err (.Os err)))
    (mapped : core.result.Result.map_err
      (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError account)
      (.Err (.Os err) : ProverRwEffectSource.Status) () = .ok (.Err .Entropy))
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (store : Store) :
    RealR1_client.prove_for_proof_accounts account pub compiled hash store state =
      .ok (.Err .Entropy,store) := by
  have callback :
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account).call_mut state 0#usize =
        .ok (.Err .Entropy,next) := by
    simp only [RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError,
      RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut,
      called,factory,mapped,bind_tc_ok,Aeneas.Std.uncurry]
  have raw_callback := callback
  dsimp only [RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError] at raw_callback
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
  rw [variant]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [prover.retry_attempt]
  simp only [prover.ATTEMPT_CAP,show ¬ (0#usize : Usize) >= 8#usize from by decide,
    if_false,raw_callback,bind_tc_ok,Aeneas.Std.uncurry]
  rfl

#print axioms factory_os_error
#print axioms client_on_factory_error
end R1Z.PV_RunJoin_SourceOsFailure
