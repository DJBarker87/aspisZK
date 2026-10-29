import R1Z.SideChannelRetryLaw
set_option autoImplicit false
namespace PV_L1D_CountSuccess
open R1Z.SideChannelL1AttemptRecord
open R1Z.ProverCommitRetry34 (Published)
variable {S P : Type}
/-- A successful return count is the initial index plus the number of entered
callbacks. The state and owner are those of the original D163 run. -/
theorem count_eq_entered (owner : Owner S P) (fuel index : Nat) (s : S)
    (p : Published P) (h : (run owner fuel index s).1.result = .done p) :
    p.attempts = index + (run owner fuel index s).1.attempts.length := by
  induction fuel generalizing index s with
  | zero => cases h
  | succ fuel ih =>
    cases step : owner index s with
    | mk record after =>
      cases hr : record.result with
      | done proof =>
        simp only [run,step,hr] at h ⊢
        cases h
        rfl
      | stop e => simp only [run,step,hr] at h; cases h
      | retry =>
        simp only [run,step,hr] at h ⊢
        have rest := ih (index+1) after h
        simp only [List.length_cons]
        omega
#print axioms count_eq_entered

/-- The successful account selector's 1..=8 guard follows from actual control,
not a new assumption restricting the witness. -/
theorem count_bounds (owner : Owner S P) (s : S) (p : Published P)
    (h : (run owner 8 0 s).1.result = .done p) :
    1 ≤ p.attempts ∧ p.attempts ≤ 8 := by
  have count := count_eq_entered owner 8 0 s p h
  have upper := attempt_cap owner 8 0 s
  have positive : 0 < (run owner 8 0 s).1.attempts.length := by
    cases step : owner 0 s with
    | mk record after =>
      cases hr : record.result <;> simp only [run,step,hr,List.length_cons] <;> omega
  omega
#print axioms count_bounds
end PV_L1D_CountSuccess
