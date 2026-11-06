import NLR_PrepareSemantic137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_ConvertedReply
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Canonical source conversion is an equivalence on the COMPLETE Verified,
not a field projection. This inversion is only a reached success branch. -/
theorem success (r : Result (NLJ_Observed.Out Unit)) (sem : r1_semantic.Verified Unit)
 (returned : NLR_PrepareSemantic137.reply r=ok (.Ok sem)) :
 r=ok (.Ok ((S1SemanticCarrier.semanticEquiv Unit).symm sem)) := by
 cases r with
 | fail e => cases returned
 | div => cases returned
 | ok r =>
  cases r with
  | Err e => cases returned
  | Ok old =>
   dsimp only [NLR_PrepareSemantic137.reply,NLR_PrepareSemantic137.convert] at returned
   have converted := core.result.Result.Ok.inj (Result.ok.inj returned)
   have oldEq : old=(S1SemanticCarrier.semanticEquiv Unit).symm sem := by
    apply (S1SemanticCarrier.semanticEquiv Unit).injective
    exact converted.trans ((S1SemanticCarrier.semanticEquiv Unit).apply_symm_apply sem).symm
   rw [oldEq]
#print axioms success
end AspisR1.NLR_ConvertedReply
end
