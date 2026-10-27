import R1Z.ProverCommitRetry34
set_option autoImplicit false
namespace R1Z.PV_OptB_ControlRelation
open Aeneas Aeneas.Std Result ProverCommitRetry34

/-- Exact error and public-state synchronization. Private successful proof
payloads may differ; no observer or failure information is erased by this
relation unless its public-state projection has separately been justified. -/
inductive Related {S T P Q : Type} (R : S → T → Prop) :
    Result (Step P × S) → Result (Step Q × T) → Prop
  | failed (e : Aeneas.Std.Error) : Related R (.fail e) (.fail e)
  | diverged : Related R .div .div
  | done (p : P) (q : Q) (s : S) (t : T) : R s t → Related R (.ok (.done p,s)) (.ok (.done q,t))
  | retry (s : S) (t : T) : R s t → Related R (.ok (.retry,s)) (.ok (.retry,t))
  | stop (e : ProverCommitRetry34.Error) (s : S) (t : T) : R s t → Related R (.ok (.stop e,s)) (.ok (.stop e,t))

/-- A sufficient control obligation at all entered states. No source body
satisfies it merely because its OS reply tape is witness-independent. -/
theorem run_related {S T P Q : Type} (R : S → T → Prop)
    (left : Attempt S P) (right : Attempt T Q)
    (step : ∀ i s t, i < 8 → R s t → Related R (left i s) (right i t))
    (fuel index : Nat) (s : S) (t : T) (bound : index+fuel ≤ 8) (same : R s t) :
    Related R (run left fuel index s) (run right fuel index t) := by
  induction fuel generalizing index s t with
  | zero => exact Related.stop .AttemptsExhausted s t same
  | succ fuel ih =>
    have entered : index < 8 := by omega
    have h := step index s t entered same
    generalize hl : left index s = l at h
    generalize hr : right index t = r at h
    rw [run,run,hl,hr]
    cases h with
    | failed e => exact Related.failed e
    | diverged => exact Related.diverged
    | done p q a b same => exact Related.done (⟨p,index+1⟩ : Published P) (⟨q,index+1⟩ : Published Q) a b same
    | stop e a b same => exact Related.stop e a b same
    | retry a b same => exact ih (index+1) a b (by omega) same

#print axioms run_related
end R1Z.PV_OptB_ControlRelation
