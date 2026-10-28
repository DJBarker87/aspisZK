import R1Z.PV_RunJoin_RetryProjection32
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RetryFrame32
open Aeneas Aeneas.Std Result ProverCommitRetry34

/-- A returned-state frame composes through every rejected attempt and every
terminal result. It asserts no frame for an account/body until its one-step
law is proved, and requires neither successful publication nor entropy. -/
theorem run {S P F : Type} (frame : S → F) (attempt : Attempt S P)
    (step : ∀ index s status next,
      attempt index s=ok (status,next) → frame next=frame s)
    (fuel index : Nat) (s next : S) (status : Step (Published P))
    (h : ProverCommitRetry34.run attempt fuel index s=ok (status,next)) :
    frame next=frame s := by
  induction fuel generalizing index s with
  | zero =>
    have he := Result.ok.inj h
    exact congrArg (fun pair => frame pair.2) he.symm
  | succ fuel ih =>
    cases ha : attempt index s with
    | fail e => simp only [ProverCommitRetry34.run,ha,bind_tc_fail] at h; cases h
    | div => simp only [ProverCommitRetry34.run,ha,bind_tc_div] at h; cases h
    | ok pair =>
      rcases pair with ⟨result,after⟩
      have hf := step index s result after ha
      cases result with
      | done proof =>
        simp only [ProverCommitRetry34.run,ha,bind_tc_ok,Aeneas.Std.uncurry] at h
        exact (congrArg (fun pair => frame pair.2) (Result.ok.inj h).symm).trans hf
      | stop e =>
        simp only [ProverCommitRetry34.run,ha,bind_tc_ok,Aeneas.Std.uncurry] at h
        exact (congrArg (fun pair => frame pair.2) (Result.ok.inj h).symm).trans hf
      | retry =>
        simp only [ProverCommitRetry34.run,ha,bind_tc_ok,Aeneas.Std.uncurry] at h
        exact (ih (index+1) after h).trans hf
#print axioms run
end R1Z.PV_RunJoin_RetryFrame32
