import AspisR1ProverStep8.Funs

/-! Row-wise composition of the extracted balancing transitions. The rows
remain symbolic; no 1024-row reduction or finite-field computation occurs.
The source iterator-to-list transport remains an execution obligation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitFoldSteps
open Aeneas Aeneas.Std Result AspisR1ProverStep8

def foldSteps {S R : Type} (step : R → S → Result S) : List R → S → Result S
  | [], s => ok s
  | r::rs, s => do let after ← step r s; foldSteps step rs after

theorem foldSteps_congr {S R : Type} (left right : R → S → Result S)
    (same : ∀ r s, left r s = right r s) (rows : List R) (s : S) :
    foldSteps left rows s = foldSteps right rows s := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp only [foldSteps, same]
    cases h : right r s with
    | fail e => rfl
    | div => rfl
    | ok after => exact ih after

def filteredStep {S R : Type} (add : S → S → Result S)
    (value : R → S) (selected : R → Bool) (r : R) (sum : S) : Result S :=
  if selected r then add sum (value r) else ok sum

theorem m31_row (sum value : aspis_core.field.M31) (active : Bool)
    (row dependent : Usize) :
    prover_commit_reference.balance_m31_step sum value active row dependent =
      (if !active && row != dependent then aspis_core.field.M31.add sum value else ok sum) := by
  cases active <;> by_cases h : row = dependent <;>
    simp [prover_commit_reference.balance_m31_step, h]

theorem qm31_row (sum value : aspis_core.field.QM31) (active : Bool)
    (row dependent : Usize) :
    prover_commit_reference.balance_qm31_step sum value active row dependent =
      (if !active && row != dependent then aspis_core.field.QM31.add sum value else ok sum) := by
  cases active <;> by_cases h : row = dependent <;>
    simp [prover_commit_reference.balance_qm31_step, h]

theorem m31_fold (rows : List Usize) (value : Usize → aspis_core.field.M31)
    (active : Usize → Bool) (dependent : Usize) (sum : aspis_core.field.M31) :
    foldSteps (fun row sum => prover_commit_reference.balance_m31_step
      sum (value row) (active row) row dependent) rows sum =
    foldSteps (filteredStep aspis_core.field.M31.add value
      (fun row => !active row && row != dependent)) rows sum := by
  apply foldSteps_congr
  intro row sum
  exact m31_row sum (value row) (active row) row dependent

theorem qm31_fold (rows : List Usize) (value : Usize → aspis_core.field.QM31)
    (active : Usize → Bool) (dependent : Usize) (sum : aspis_core.field.QM31) :
    foldSteps (fun row sum => prover_commit_reference.balance_qm31_step
      sum (value row) (active row) row dependent) rows sum =
    foldSteps (filteredStep aspis_core.field.QM31.add value
      (fun row => !active row && row != dependent)) rows sum := by
  apply foldSteps_congr
  intro row sum
  exact qm31_row sum (value row) (active row) row dependent

#print axioms foldSteps_congr
#print axioms m31_row
#print axioms qm31_row
#print axioms m31_fold
#print axioms qm31_fold
end R1Z.ProverCommitFoldSteps
