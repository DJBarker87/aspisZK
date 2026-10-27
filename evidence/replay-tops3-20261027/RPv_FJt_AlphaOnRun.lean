import RPv_FJa_ClaimsOnRun
import RPv_FIr_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_AlphaOnRun
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Isolate accepted-source alpha canonicality at a symbolic boundary, so
instantiating the concrete FIq dictionary never unfolds its terminal body. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem)) :
    ∀ x∈(retainedSem sem).alpha.val,FIp_SemanticValues.Canon x := by
  have source : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub bytes hash=ok (.Ok sem) := accepted
  exact FIr_AlphaCanonical.verified (ClaimsUnrolledFinish.install std B) D pub bytes hash sem source
#print axioms value
end AspisR1.FJt_AlphaOnRun
end
