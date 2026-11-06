import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_allocate (cfg : Configuration) {H : Type} (s : State H)  : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let n ← compact.LOGICAL_SEMANTIC o
 let ny ← compact.LOGICAL_Y1
 let total ← n + ny
 let r ← o.op1 core.marker.CopyU8 total 0#u8
 match r with
 | .Err _ => pure (.inl (.Err verifier.Error.Allocation,i.scratch))
 | .Ok logical => pure (.inr (advance s (.split n logical)))
theorem step_allocate (cfg : Configuration) {H : Type} (s : State H) 
 (atSite : s.locals = .allocate ) : step cfg s = window_allocate cfg s  := by
 simp only [step,atSite]
 try rfl
#print axioms step_allocate
end AspisR1.NLJ_Prepare
end
