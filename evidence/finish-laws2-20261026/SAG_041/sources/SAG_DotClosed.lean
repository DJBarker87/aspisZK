import SAG_DotAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_DotClosed
open Aeneas Aeneas.Std Result
abbrev PushState := AspisR1FinishDotDecodedProductTrace.PushState

/-- Seed fields are unused by the concretely installed dot body. -/
def seed : AspisR1FinishRelationCurrent.FinishOps Unit PushState where
  eq := fun _ _ => div
  add := fun _ _ => div
  mulM31 := fun _ _ => div
  quarter := div
  newWeights := fun _ _ _ => div
  pair := fun _ _ _ _ => div
  field := fun _ _ => div
  newDot := div
  pushDot := fun _ _ _ => div
  finishDot := fun _ => div
  polynomial := fun _ _ => div

def source := SAG_DotAdapter.sourceDot seed

theorem kernel_independent {A B : Type}
    (a : AspisR1FinishRelationCurrent.FinishOps A PushState)
    (b : AspisR1FinishRelationCurrent.FinishOps B PushState)
    (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K) :
    SAG_DotAdapter.kernel a fm ws = SAG_DotAdapter.kernel b fm ws := rfl

theorem source_independent {A : Type}
    (a : AspisR1FinishRelationCurrent.FinishOps A PushState) :
    SAG_DotAdapter.sourceDot a = source := by
  funext fm ws
  unfold SAG_DotAdapter.sourceDot source
  rw [kernel_independent a seed]
  rfl

#print axioms kernel_independent
#print axioms source_independent
end AspisR1.SAG_DotClosed
end
