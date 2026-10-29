import PV_DIAG2_Exit
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34

/-- Exhaustion does not format any witness operand. This is the caller's
normal report request only; callee effects and captured-frame law remain. -/
theorem cap_requested_text {S P : Type} (a : Nat → S → Observed (Step P × S))
    (k : Nat) (s : S) (pcs : List Nat) :
 (finish ⟨false,pcs,""⟩ (runEffects a 0 k s)).effects =
 [.returned .AttemptsExhausted,.stderr "Error: AttemptsExhausted\n"] := by
 simpa [runEffects,exportError,spelling] using
   stopped_report (runEffects a 0 k s) .AttemptsExhausted s pcs rfl

/-- A body retry retains the full failed-attempt effects on the path to cap. -/
theorem last_rejection_reports {S P : Type} (a : Nat → S → Observed (Step P × S))
    (k : Nat) (s after : S) (h : (a k s).result = ok (.retry,after)) (pcs : List Nat) :
 (finish ⟨false,pcs,""⟩ (runEffects a 1 k s)).effects =
 .entered k :: ((a k s).effects ++ [.rejected k,
   .returned .AttemptsExhausted,.stderr "Error: AttemptsExhausted\n"]) := by
 rw [rejected_effects a 0 k s after h]
 simp [finish,runEffects,report_disabled,exportError,spelling,List.append_assoc]

/-- The source Result includes the final state even when the final event is
exhaustion. No attempt/error history or failed write is erased by this fact. -/
theorem cap_full_result {S P : Type} (a : Nat → S → Observed (Step P × S))
    (k : Nat) (s : S) :
 (runEffects a 0 k s).result = ok (.stop .AttemptsExhausted,s) := rfl

#print axioms cap_requested_text
#print axioms last_rejection_reports
#print axioms cap_full_result
end PV_DIAG2
