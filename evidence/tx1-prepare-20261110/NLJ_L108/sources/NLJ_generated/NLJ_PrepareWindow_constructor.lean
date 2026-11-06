import NLJ_PrepareStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code)
/-- Exact occurrence body, retaining full Result/owner/back-function/scratch
carry. Native realization and caller child-domain installation remain OPEN. -/
def window_constructor (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H) : Code (Post H) := do
 let i := s.input
 let o := ops cfg
 let out ← BorrowedClaimPrepared.closedPreparationCode i.digest sem v i.hash i.scratch
 pure (.inl out)
theorem step_constructor (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H)
 (atSite : s.locals = .constructor logical v sem) : step cfg s = window_constructor cfg s logical v sem := by
 simp only [step,atSite]
 try rfl
#print axioms step_constructor
end AspisR1.NLJ_Prepare
end
