import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_expandSemantic (cfg : Configuration) {H : Type} (s : State H) (n offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let (r,semanticAfter) ← o.op10 compressed semantic
 match r with
 | .Ok _ => pure (.inr (advance s (.valueRange n offY1 semanticAfter y1 splitBack vecBack)))
 | .Err e =>
   let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared (verifier.Error.Insts.CoreConvertFromCodecError o) (.Err e)
   pure (.inl (r,i.scratch))
theorem step_expandSemantic (cfg : Configuration) {H : Type} (s : State H) (n offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .expandSemantic n offY1 semantic y1 compressed splitBack vecBack) : step cfg s = window_expandSemantic cfg s n offY1 semantic y1 compressed splitBack vecBack := by
 simp only [step,atSite]
 try rfl
#print axioms step_expandSemantic
end AspisR1.NLJ_Prepare
end
