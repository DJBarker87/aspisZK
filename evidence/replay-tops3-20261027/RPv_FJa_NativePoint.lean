import RPv_FIr_AlphaCanonical
import RPv_FIr_CarrierCanonical
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_NativePoint
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
/-- Canonicality of the SAME alpha point passed by the installed FIq terminal,
derived from its accepted semantic reader. -/
theorem verified {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify
      AspisS1ExtractedRoundChildren.children B D pub bytes hash=ok (.Ok sem)) :
    FIw_ArrayValue.canonical (FIq_Carriers.mapArray FIq_Carriers.toQ (retainedSem sem).alpha) := by
  exact FIr_CarrierCanonical.array _ (FIr_AlphaCanonical.verified B D pub bytes hash sem success)
#print axioms verified
end AspisR1.FJa_NativePoint
end
