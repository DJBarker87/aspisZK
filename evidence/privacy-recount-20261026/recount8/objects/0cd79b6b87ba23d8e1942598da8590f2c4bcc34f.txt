import R1Z.PV_RunJoin_UnifiedRetry
import R1Z.PV_RunJoin_ResultTransport
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RetryProjection32
open Aeneas Aeneas.Std Result ProverCommitRetry34 ProverCommitSemanticTransport26

/-- A one-attempt complete-Result simulation extends to the entire retry
machine, retaining rejected-attempt states, terminal errors, divergence,
proofs and publication attempt counts. No fairness or successful-entropy
premise is introduced. -/
theorem run {S T P : Type} (project : S → T)
    (left : Attempt S P) (right : Attempt T P)
    (step : ∀ index s,
      mapR (fun out => (out.1,project out.2)) (left index s) = right index (project s))
    (fuel index : Nat) (s : S) :
    mapR (fun out => (out.1,project out.2)) (ProverCommitRetry34.run left fuel index s) =
      ProverCommitRetry34.run right fuel index (project s) := by
  induction fuel generalizing index s with
  | zero => rfl
  | succ fuel ih =>
    simp only [ProverCommitRetry34.run]
    rw [← step index s]
    cases h : left index s with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨status,next⟩
      cases status with
      | done proof => rfl
      | stop e => rfl
      | retry => exact ih (index+1) next
#print axioms run

theorem eight {S T P : Type} (project : S → T)
    (left : Attempt S P) (right : Attempt T P)
    (step : ∀ index s,
      mapR (fun out => (out.1,project out.2)) (left index s) = right index (project s))
    (s : S) :
    mapR (fun out => (out.1,project out.2)) (ProverCommitRetry34.eight left s) =
      ProverCommitRetry34.eight right (project s) := run project left right step 8 0 s
#print axioms eight
end R1Z.PV_RunJoin_RetryProjection32
