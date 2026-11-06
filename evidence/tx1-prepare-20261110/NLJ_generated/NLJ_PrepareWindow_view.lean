import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_view (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let r ← o.op5 i.proof semantic y1
 match r with
 | .Err e => pure (.inl (.Err e,i.scratch))
 | .Ok v => pure (.inr (advance s (.semantic logical v)))
theorem step_view (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 (atSite : s.locals = .view logical semantic y1) : step cfg s = window_view cfg s logical semantic y1 := by
 simp only [step,atSite]
 try rfl
#print axioms step_view
end AspisR1.NLJ_Prepare
end
