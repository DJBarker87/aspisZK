import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_semantic (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let r ← S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install cfg.std cfg.boundaries) i.digest i.publicValue v.semantic i.hash
 pure (.inr (advance s (.mapSemantic logical v r)))
theorem step_semantic (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View)
 (atSite : s.locals = .semantic logical v) : step cfg s = window_semantic cfg s logical v := by
 simp only [step,atSite]
 try rfl
#print axioms step_semantic
end AspisR1.NLJ_Prepare
end
