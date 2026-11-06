import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_semanticRange (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let off ← compact.OFF_SEMANTIC o
 let offY1 ← compact.OFF_Y1 o
 let compressed ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=off,«end»:=offY1}
 pure (.inr (advance s (.expandSemantic n offY1 semantic y1 compressed splitBack vecBack)))
theorem step_semanticRange (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .semanticRange n semantic y1 splitBack vecBack) : step cfg s = window_semanticRange cfg s n semantic y1 splitBack vecBack := by
 simp only [step,atSite]
 try rfl
#print axioms step_semanticRange
end AspisR1.NLJ_Prepare
end
