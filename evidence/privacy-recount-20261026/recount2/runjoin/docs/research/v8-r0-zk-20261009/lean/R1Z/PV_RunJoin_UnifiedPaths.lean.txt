import R1Z.PV_RunJoin_UnifiedRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_UnifiedPaths
open Aeneas Aeneas.Std Result ProverRwRngCaller
open PV_RunJoin_UnifiedRetry
variable [ProverRwFull.ExternalTypes] [NativeTypes] [ErasureFns]
variable {N L C : Type}
variable (account : ProverRwEffectCallback.Account (State N L C)) (body : Body (State N L C))
variable (index : Nat) (s next final : State N L C)

theorem entropy_error (nonce : Array U8 32#usize) (provider : Tape)
    (error : StateOnlyAttemptEntropyError)
    (policy : account.call_mut s (ProverCommitRetrySource34.word index) = .ok (nonce,next))
    (owner : StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce next.provider =
      .ok (provider,.Err error)) :
    entropy account index s = .ok (.Err .Entropy,{next with provider := provider}) := by
  simp only [entropy,policy,owner,bind_tc_ok,Aeneas.Std.uncurry]

theorem entropy_success (nonce : Array U8 32#usize) (provider : Tape)
    (secret : StateOnlyAttemptSecrets)
    (policy : account.call_mut s (ProverCommitRetrySource34.word index) = .ok (nonce,next))
    (owner : StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce next.provider =
      .ok (provider,.Ok secret)) :
    entropy account index s = .ok (.Ok (PV_RunJoin_SourceBinding.secret secret),{next with provider := provider}) := by
  simp only [entropy,policy,owner,bind_tc_ok,Aeneas.Std.uncurry]

theorem stopped_entropy (error : ProverRwFull.verifier.Error)
    (he : entropy account index s = .ok (.Err error,next)) :
    attempt account body index s = .ok (.stop (ProverRwRetryModel.error error),next) := by
  simp only [attempt,he,bind_tc_ok,Aeneas.Std.uncurry]

theorem rejected (secret : ProverRwRetryModel.Secret)
    (he : entropy account index s = .ok (.Ok secret,next))
    (hb : body secret next = .ok (.Err .Rejected,final)) :
    attempt account body index s = .ok (.retry,final) := by
  simp only [attempt,he,hb,bind_tc_ok,Aeneas.Std.uncurry]

theorem successful (secret : ProverRwRetryModel.Secret) (proof : ProverRwRetryModel.Proof)
    (he : entropy account index s = .ok (.Ok secret,next))
    (hb : body secret next = .ok (.Ok proof,final)) :
    attempt account body index s = .ok (.done proof,final) := by
  simp only [attempt,he,hb,bind_tc_ok,Aeneas.Std.uncurry]

theorem fatal (secret : ProverRwRetryModel.Secret) (error : ProverRwFull.verifier.Error)
    (hf : error ≠ .Rejected)
    (he : entropy account index s = .ok (.Ok secret,next))
    (hb : body secret next = .ok (.Err error,final)) :
    attempt account body index s = .ok (.stop (ProverRwRetryModel.error error),final) := by
  cases error <;> simp_all only [attempt,he,hb,bind_tc_ok,Aeneas.Std.uncurry,ne_eq,not_true_eq_false]

/-- The next callback sees the body-returned world, including its ledger and
client/oracle context. No earlier world or zero cursor is substituted. -/
theorem rejected_next (fuel : Nat) (secret : ProverRwRetryModel.Secret)
    (he : entropy account index s = .ok (.Ok secret,next))
    (hb : body secret next = .ok (.Err .Rejected,final)) :
    ProverCommitRetry34.run (attempt account body) (fuel+1) index s =
      ProverCommitRetry34.run (attempt account body) fuel (index+1) final :=
  ProverCommitRetry34.rejected_next _ _ _ _ _ (rejected account body index s next final secret he hb)

#print axioms entropy_error
#print axioms entropy_success
#print axioms stopped_entropy
#print axioms rejected
#print axioms successful
#print axioms fatal
#print axioms rejected_next
end R1Z.PV_RunJoin_UnifiedPaths
