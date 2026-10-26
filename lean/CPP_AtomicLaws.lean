import CPP_Atomic
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicLaws
open Aeneas Aeneas.Std Result Hist_Store CPP_Atomic
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A failed transaction rolls back ALL earlier accepted CPI copies, not only
its last child. The exact final error/divergence result is retained. -/
theorem rollback {B : Type} (before : Store) (tentative : Output B) (failed : ¬ committed tentative.2.2) :
    settle before tentative = (before,[.rollback],tentative.2.2) := by
  cases value : tentative.2.2 with
  | fail e => simp only [settle,value]
  | div => simp only [settle,value]
  | ok result => cases result with
    | Err e => simp only [settle,value]
    | Ok b => exact False.elim (failed ⟨b,value⟩)

theorem commit {B : Type} (before : Store) (tentative : Output B) (success : committed tentative.2.2) :
    settle before tentative = tentative := by
  obtain ⟨b,success⟩ := success
  simp only [settle,success]

theorem reply {B : Type} (before : Store) (tentative : Output B) :
    (settle before tentative).2.2 = tentative.2.2 := by
  cases value : tentative.2.2 with
  | fail e => simp only [settle,value]
  | div => simp only [settle,value]
  | ok result => cases result <;> simp only [settle,value]

#print axioms rollback
#print axioms commit
#print axioms reply
end AspisR1.CPP_AtomicLaws
end
