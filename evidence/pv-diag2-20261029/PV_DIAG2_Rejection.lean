import PV_DIAG2_Retry
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34 ProverCommitSemanticTransport26

def RejectFree {S P : Type} (r : Result (Step P × S)) : Prop :=
 ∀ after, r ≠ ok (.stop .Rejected,after)

/-- This generic dictionary needs its equality law installed. We do not
infer native equality from an external slot's name. -/
theorem active_pole_rejected [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
    (equal : ProverRwFull.r1_wire.Error.Insts.CoreCmpPartialEqError.eq
      .ActivePole .ActivePole = ok true) :
 ProverRwFull.prover.semantic_error ProverRwFull.r1_wire.Error.ActivePole =
 ok ProverRwFull.verifier.Error.Rejected := by
 rw [ProverRwFull.prover.semantic_error,equal]
 rfl

/-- Body Rejected is consumed by the controller. The entropy callback's
error arm is different and requires its actual client binding below. -/
theorem attempt_reject_free [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
    {C : Type} (entropy : ProverRwRetryModel.Entropy C)
    (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
    (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
    (k : Nat) (state : C × ProverRwRetryModel.Store)
    (entropyNotRejected : ∀ after,
      entropy.call_mut state.1 (ProverCommitRetrySource34.word k) ≠
        ok (.Err ProverRwFull.verifier.Error.Rejected,after)) :
 RejectFree (ProverRwRetryModel.attempt entropy pub compiled variant hash k state) := by
 unfold RejectFree
 intro after
 unfold ProverRwRetryModel.attempt
 cases ent : entropy.call_mut state.1 (ProverCommitRetrySource34.word k) with
 | fail e => simp [ent]
 | div => simp [ent]
 | ok pair =>
   rcases pair with ⟨result,next⟩
   cases result with
   | Err e =>
     cases e <;> simp [ent,ProverRwRetryModel.error]
     exact False.elim (entropyNotRejected next ent)
   | Ok secret =>
     cases body : ProverRwFull.prover.prove_masked_attempt pub compiled variant hash secret state.2 with
     | fail e => simp [ent,body]
     | div => simp [ent,body]
     | ok pair =>
       rcases pair with ⟨result,store⟩
       cases result with
       | Ok p => simp [ent,body]
       | Err e => cases e <;> simp [ent,body,ProverRwRetryModel.error]

/-- Retry may exhaust, fail, diverge or return another error. It cannot leak
its consumed body-Rejected status as a final Rejected API result. -/
theorem run_reject_free {S P : Type} (a : Attempt S P)
    (ha : ∀ k s, RejectFree (a k s)) (n k : Nat) (s : S) :
 RejectFree (run a n k s) := by
 induction n generalizing k s with
 | zero => intro after h; cases h
 | succ n ih =>
   unfold run
   cases h : a k s with
   | fail e => intro after hn; simp [h] at hn
   | div => intro after hn; simp [h] at hn
   | ok pair =>
     rcases pair with ⟨step,next⟩
     cases step with
     | done p => intro after hn; simp [h] at hn
     | retry => simpa only [h,bind_tc_ok,Aeneas.Std.uncurry] using ih (k+1) next
     | stop e =>
       intro after hn
       have eq : e = .Rejected ∧ next = after := by
         simpa only [h,bind_tc_ok,Aeneas.Std.uncurry,Result.ok.injEq,Prod.mk.injEq,Step.stop.injEq] using hn
       have he := eq.1
       subst e
       exact ha k s next h

/-- Instrumentation retains all effects while the complete Result satisfies
the above exclusion. No callee-silence premise is inserted. -/
theorem observed_reject_free {S P : Type} (a : Nat → S → Observed (Step P × S))
    (ha : ∀ k s, RejectFree ((a k s).result)) (n k : Nat) (s : S) :
 RejectFree (runEffects a n k s).result := by
 rw [erase_run]
 exact run_reject_free (eraseAttempt a) ha n k s

#print axioms active_pole_rejected
#print axioms attempt_reject_free
#print axioms run_reject_free
#print axioms observed_reject_free
end PV_DIAG2
