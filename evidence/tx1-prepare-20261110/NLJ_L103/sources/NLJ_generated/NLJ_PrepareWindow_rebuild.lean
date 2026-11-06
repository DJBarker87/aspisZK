import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_rebuild (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let logical := vecBack (splitBack (semantic,y1))
 let semanticFull ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) logical {«end»:=n}
 let y1Full ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) logical {start:=n}
 pure (.inr (advance s (.view logical semanticFull y1Full)))
theorem step_rebuild (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .rebuild n semantic y1 splitBack vecBack) : step cfg s = window_rebuild cfg s n semantic y1 splitBack vecBack := by
 simp only [step,atSite]
 try rfl
#print axioms step_rebuild
end AspisR1.NLJ_Prepare
end
