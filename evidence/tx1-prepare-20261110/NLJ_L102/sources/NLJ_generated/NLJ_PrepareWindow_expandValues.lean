import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_expandValues (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let (r,y1After) ← o.op11 compressed y1
 match r with
 | .Ok _ => pure (.inr (advance s (.rebuild n semantic y1After splitBack vecBack)))
 | .Err e =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
   pure (.inl (r,i.scratch))
theorem step_expandValues (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .expandValues n semantic y1 compressed splitBack vecBack) : step cfg s = window_expandValues cfg s n semantic y1 compressed splitBack vecBack := by
 simp only [step,atSite]
 try rfl
#print axioms step_expandValues
end AspisR1.NLJ_Prepare
end
