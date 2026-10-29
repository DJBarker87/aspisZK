import R1Z.ProverCommitRetry34
set_option autoImplicit false
namespace PV_FIB_Termination
open Aeneas Aeneas.Std Result
open R1Z.ProverCommitRetry34

/-- Finite retry fuel does not prove callback termination. With callback
termination supplied, it excludes divergence on ALL branches, not just done. -/
theorem run_not_div {S P : Type} (attempt : Attempt S P)
    (total : ∀ i s, attempt i s ≠ .div)
    (fuel index : Nat) (state : S) : run attempt fuel index state ≠ .div := by
  induction fuel generalizing index state with
  | zero => intro h; cases h
  | succ fuel ih =>
    unfold run
    cases ha : attempt index state with
    | div => exact False.elim (total index state ha)
    | fail e => intro h; cases h
    | ok pair =>
      rcases pair with ⟨step, after⟩
      cases step with
      | done p => intro h; cases h
      | stop e => intro h; cases h
      | retry => exact ih (index+1) after

/-- A stopped/error Result is a normal finite result, and is NOT thereby a
member of the probabilistic charged bad event. -/
theorem zero_fuel {S P : Type} (attempt : Attempt S P) (index : Nat) (s : S) :
    run attempt 0 index s = .ok (.stop .AttemptsExhausted,s) := rfl

#print axioms run_not_div
#print axioms zero_fuel
end PV_FIB_Termination
