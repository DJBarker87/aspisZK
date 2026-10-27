import RPz8_ARW_Induced
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_SubmissionBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- The numerical model may keep only the first submission; its actual issued
cost is bounded by the full induced adversary cost, without discarding the
second choice from the charged account. -/
theorem bound {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : SCE_Experiment.Adversary A)
    (Q : Nat) (queries : ∀ H, (ARW_Induced.issued native1 copy allocator id a H).length ≤ Q) :
    ∀ H, (eval H (SCE_Experiment.submission a)).1.length ≤ Q := by
  intro H
  have q := queries H
  simp only [SCE_Experiment.submission_eval,ARW_Induced.issued,List.length_append] at *
  omega
#print axioms bound
end AspisR1.ARX_SubmissionBudget
end
