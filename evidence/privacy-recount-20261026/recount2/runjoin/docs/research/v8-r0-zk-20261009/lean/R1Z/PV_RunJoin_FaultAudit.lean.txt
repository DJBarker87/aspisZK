import R1Z.PV_RunJoin_UnifiedRetry
import R1Z.ProverRwRngCallerEntropy
import R1Z.PV_RunJoin_KernelCompletion
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FaultAudit
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
variable [ProverRwFull.ExternalTypes] [NativeTypes] [ErasureFns]

/-- An entered native-size draw can fail after arbitrary partial writes. The
emitted owner returns the advanced provider and exact OS error; no successful
seed or availability premise is used. This is control, not native adequacy. -/
theorem owner_os_error (p after : Tape) (nonce : Array U8 32#usize)
    (entered : entropy_nonzero32 nonce = .ok true)
    (written : Array U8 64#usize) (error : getrandom.error.Error)
    (reply : Tape.Insts.Prover_rw_rng_callerDraw64.fill p (Array.repeat 64#usize 0#u8) =
      .ok ((after,.Err error),written)) :
    StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce p =
      .ok (after,.Err (.Os error)) := by
  have step := ProverRwRngCallerEntropy.error_state
    Tape.Insts.Prover_rw_rng_callerDraw64 p after nonce 0#usize 16#usize
    (by decide) written error reply
  unfold StateOnlyAttemptSecrets.generate_with
  rw [entered]
  simp only [bind_tc_ok,if_true,ENTROPY_RETRY_LIMIT]
  unfold StateOnlyAttemptSecrets.generate_with_loop
  rw [loop]
  simpa only [step,bind_tc_ok] using step

/-- Exact first-attempt failure in the endpoint's shared-world client. The
body is arbitrary and never entered. This includes the returned account world
and advanced draw provider; a retry or a fresh-world restart would be wrong. -/
theorem client_os_error {N L C : Type}
    (account : ProverRwEffectCallback.Account (PV_RunJoin_UnifiedRetry.State N L C))
    (body : PV_RunJoin_UnifiedRetry.Body (PV_RunJoin_UnifiedRetry.State N L C))
    (s next : PV_RunJoin_UnifiedRetry.State N L C)
    (nonce : Array U8 32#usize) (after : Tape)
    (policy : account.call_mut s (ProverCommitRetrySource34.word 0) = .ok (nonce,next))
    (entered : entropy_nonzero32 nonce = .ok true)
    (written : Array U8 64#usize) (error : getrandom.error.Error)
    (reply : Tape.Insts.Prover_rw_rng_callerDraw64.fill next.provider (Array.repeat 64#usize 0#u8) =
      .ok ((after,.Err error),written)) :
    PV_RunJoin_UnifiedRetry.client account body s =
      .ok (.stop .Entropy,{next with provider := after}) := by
  have owner := owner_os_error next.provider after nonce entered written error reply
  have stopped : PV_RunJoin_UnifiedRetry.attempt account body 0 s =
      .ok (.stop .Entropy,{next with provider := after}) := by
    simp only [PV_RunJoin_UnifiedRetry.attempt,PV_RunJoin_UnifiedRetry.entropy,
      policy,owner,bind_tc_ok,Aeneas.Std.uncurry,ProverRwRetryModel.error]
  change ProverCommitRetry34.run _ 8 0 s = _
  rw [ProverCommitRetry34.run,stopped]
  rfl

/-- Zero successful-return availability satisfies the conditional E1 kernel
law. This refutes any inference of an always-successful native draw from E1;
it does not refute privacy with a correctly transported public fault world. -/
theorem E1_allows_total_failure {C R E : Type} [Fintype R]
    (fault : C → E → ℚ) :
    PV_RunJoin_KernelCompletion.E1
      (PV_RunJoin_KernelCompletion.Kernel.mk (fun _ => 0) (fun _ (_ : R) => 0) fault) ∧
    ∀ c : C, (PV_RunJoin_KernelCompletion.Kernel.mk
      (fun _ : C => (0 : ℚ)) (fun _ (_ : R) => 0) fault).successMass c = 0 :=
  ⟨PV_RunJoin_KernelCompletion.zero_success fault,fun _ => rfl⟩

#print axioms owner_os_error
#print axioms client_os_error
#print axioms E1_allows_total_failure
end R1Z.PV_RunJoin_FaultAudit
