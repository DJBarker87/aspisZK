import R1Z.ProverCommitRetry34
import R1Z.PV_OptB_Factorization
set_option autoImplicit false
namespace R1Z.PV_OptB_RetryControl
open Aeneas Aeneas.Std Result ProverCommitRetry34

/-- Raw control counterexample, not an admitted-witness/source-body instance.
Both branches see the same potential OS fault at attempt 1. Only the retrying
branch reaches it. This checks why a tape-only argument is insufficient. -/
def probeAttempt (reject : Bool) : Attempt Nat Unit := fun i state =>
  if i = 0 then
    if reject then .ok (.retry,state+1) else .ok (.done (),state+1)
  else .ok (.stop .Entropy,state+1)

inductive Failure where
  | entropy (attempt entered : Nat)
  deriving DecidableEq

def failureOf : Result (Step (Published Unit) × Nat) → Option Failure
  | .ok (.stop .Entropy,entered) => some (.entropy (entered-1) entered)
  | _ => none

theorem accepts_before_fault :
    failureOf (eight (probeAttempt false) 0) = none := rfl

theorem retries_into_fault :
    failureOf (eight (probeAttempt true) 0) = some (.entropy 1 2) := rfl

theorem fixed_potential_fault_is_insufficient :
    ¬ PV_OptB_Factorization.Independent (fun _ : Bool => ())
      (fun reject (_ : Unit) (_ : Unit) => failureOf (eight (probeAttempt reject) 0)) := by
  intro independent
  have same := independent false true rfl () ()
  change failureOf (eight (probeAttempt false) 0) = failureOf (eight (probeAttempt true) 0) at same
  rw [accepts_before_fault,retries_into_fault] at same
  cases same

#print axioms accepts_before_fault
#print axioms retries_into_fault
#print axioms fixed_potential_fault_is_insufficient
end R1Z.PV_OptB_RetryControl
