import R1Z.PV_OptB_OffBadJoin
set_option autoImplicit false
namespace R1Z.PV_OptB_BodySync
open Aeneas Aeneas.Std Result
open PV_OptB_ControlRelation PV_RunJoin_UnifiedRetry
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

/-- Exact body errors and state relation; successful private proof bytes may
vary. This is a proof obligation, not a replacement body or trust field. -/
inductive BodyRelated {S T : Type} (R : S → T → Prop) :
    Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × S) →
    Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × T) → Prop
  | failed (e : Aeneas.Std.Error) : BodyRelated R (.fail e) (.fail e)
  | diverged : BodyRelated R .div .div
  | success (p q : ProverRwRetryModel.Proof) (s : S) (t : T) :
      R s t → BodyRelated R (.ok (.Ok p,s)) (.ok (.Ok q,t))
  | error (e : ProverRwFull.verifier.Error) (s : S) (t : T) :
      R s t → BodyRelated R (.ok (.Err e,s)) (.ok (.Err e,t))

def finish {S : Type}
    (r : Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × S)) :
    Result (ProverCommitRetry34.Step ProverRwRetryModel.Proof × S) := do
  let (status,after) ← r
  match status with
  | .Ok proof => .ok (.done proof,after)
  | .Err .Rejected => .ok (.retry,after)
  | .Err e => .ok (.stop (ProverRwRetryModel.error e),after)

#print axioms finish
theorem finish_related {S T : Type} (R : S → T → Prop)
    (left : Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × S))
    (right : Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × T))
    (same : BodyRelated R left right) : Related R (finish left) (finish right) := by
  cases same with
  | failed e => exact Related.failed e
  | diverged => exact Related.diverged
  | success p q s t h => exact Related.done p q s t h
  | error e s t h =>
    cases e <;> first | exact Related.retry s t h | exact Related.stop _ s t h

#print axioms finish_related
theorem attempt_finish {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s next : State N L C)
    (secret : ProverRwRetryModel.Secret)
    (called : entropy account i s = .ok (.Ok secret,next)) :
    attempt account body i s = finish (body secret next) := by
  simp only [attempt,called,bind_tc_ok,Aeneas.Std.uncurry,finish]
  rfl

#print axioms attempt_finish
theorem attempt_entropy_error {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s next : State N L C)
    (e : ProverRwFull.verifier.Error)
    (called : entropy account i s = .ok (.Err e,next)) :
    attempt account body i s = .ok (.stop (ProverRwRetryModel.error e),next) := by
  simp only [attempt,called,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms attempt_entropy_error
theorem attempt_entropy_fail {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s : State N L C)
    (e : Aeneas.Std.Error) (called : entropy account i s = .fail e) :
    attempt account body i s = .fail e := by
  simp only [attempt,called,bind_tc_fail]

#print axioms attempt_entropy_fail
theorem attempt_entropy_div {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s : State N L C)
    (called : entropy account i s = .div) : attempt account body i s = .div := by
  simp only [attempt,called,bind_tc_div]

#print axioms attempt_entropy_div
theorem attempt_related_at_same_state {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (left right : Body (State N L C)) (i : Nat) (s : State N L C)
    (body_law : ∀ secret next, BodyRelated Eq (left secret next) (right secret next)) :
    Related Eq (attempt account left i s) (attempt account right i s) := by
  cases called : entropy account i s with
  | fail e => rw [attempt_entropy_fail account left i s e called,attempt_entropy_fail account right i s e called]; exact Related.failed e
  | div => rw [attempt_entropy_div account left i s called,attempt_entropy_div account right i s called]; exact Related.diverged
  | ok pair =>
    rcases pair with ⟨status,next⟩
    cases status with
    | Err e =>
      rw [attempt_entropy_error account left i s next e called,attempt_entropy_error account right i s next e called]
      exact Related.stop _ next next rfl
    | Ok secret =>
      rw [attempt_finish account left i s next secret called,attempt_finish account right i s next secret called]
      exact finish_related Eq _ _ (body_law secret next)

#print axioms attempt_related_at_same_state
end R1Z.PV_OptB_BodySync
