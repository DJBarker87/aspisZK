import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SubmissionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

theorem queries {A : Type} (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (H : Bytes → State) :
    (eval H (submission a)).1.length ≤ Q0+Q1 := by
  rw [submission_eval]
  exact (prefixBound H).trans (Nat.le_add_right _ _)

#print axioms queries
end AspisR1.SCE_SubmissionBound
end
