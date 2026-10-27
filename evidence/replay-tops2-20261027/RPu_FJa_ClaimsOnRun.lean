import RPu_FJa_ClaimsCanonical
import RPz7_ClaimsUnrolledVerify
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ClaimsOnRun
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- Native claim canonicality on the SAME selected semantic call, using the
installed Claims decoder and preserving its actual returned claim array. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem)) :
    ∀ row∈(retainedSem sem).claims.val,∀ q∈row.val,FIp_SemanticValues.Canon q := by
  obtain ⟨pre,initial,after,challenges,_,_,_,_,reference⟩ :=
    ClaimsUnrolledSdk.semantic_claims std ops B D pub bytes hash sem accepted
  exact FJa_ClaimsCanonical.value std pre (retainedSem sem).claims reference
#print axioms value
end AspisR1.FJa_ClaimsOnRun
end
