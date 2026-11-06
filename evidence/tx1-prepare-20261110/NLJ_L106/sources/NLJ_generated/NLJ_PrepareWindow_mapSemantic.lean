import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_mapSemantic (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 match r with
 | .Err _ => pure (.inl (.Err verifier.Error.Semantic,i.scratch))
 | .Ok sem => pure (.inr (advance s (.mark logical v sem)))
theorem step_mapSemantic (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error)
 (atSite : s.locals = .mapSemantic logical v r) : step cfg s = window_mapSemantic cfg s logical v r := by
 simp only [step,atSite]
 try rfl
#print axioms step_mapSemantic
end AspisR1.NLJ_Prepare
end
