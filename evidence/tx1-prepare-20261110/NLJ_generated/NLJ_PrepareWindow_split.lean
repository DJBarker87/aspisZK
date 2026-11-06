import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_split (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (logical : alloc.vec.Vec U8) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let (bytes,vecBack) ← lift (alloc.vec.Vec.deref_mut logical)
 let ((semantic,y1),splitBack) ← core.slice.Slice.split_at_mut bytes n
 pure (.inr (advance s (.semanticRange n semantic y1 splitBack vecBack)))
theorem step_split (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (logical : alloc.vec.Vec U8)
 (atSite : s.locals = .split n logical) : step cfg s = window_split cfg s n logical := by
 simp only [step,atSite]
 try rfl
#print axioms step_split
end AspisR1.NLJ_Prepare
end
