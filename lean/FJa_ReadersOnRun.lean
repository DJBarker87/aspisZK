import FJa_ClaimsOnRun
import FJa_NativePoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ReadersOnRun
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
/-- SAME accepted source call derives both claim-reader and point-reader
canonicality on precisely the FIq carrier conversions. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem)) :
    FIr_GatherCallback.CanonClaims (FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ)
      (retainedSem sem).claims) ∧
    FIw_ArrayValue.canonical (FIq_Carriers.mapArray FIq_Carriers.toQ (retainedSem sem).alpha) := by
  have verified : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub bytes hash=ok (.Ok sem) := accepted
  exact ⟨FIr_CarrierCanonical.claims _ (FJa_ClaimsOnRun.value std ops B D pub bytes hash sem accepted),
    FJa_NativePoint.verified _ D pub bytes hash sem verified⟩
#print axioms value
end AspisR1.FJa_ReadersOnRun
end
