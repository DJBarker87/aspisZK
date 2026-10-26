import F3V_OracleDictionary
import F3V_SemanticVerify
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_CurrentSemantic
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : Hash) :
    F3U_Rehash.code H (AspisR1CurrentCaller.S1SemanticCodeInstallation.code R B D pub bytes hash)=
      AspisR1CurrentCaller.S1SemanticCodeInstallation.code R B (F3V_OracleDictionary.current H D) pub bytes hash := by
  simp only [AspisR1CurrentCaller.S1SemanticCodeInstallation.code,F3U_RehashBind.bind,
    F3V_OracleDictionary.retained,F3V_SemanticVerify.same]
  apply congrArg (fun k => _ >>= k)
  funext x
  rfl

#print axioms same
end AspisR1.F3V_CurrentSemantic
end
