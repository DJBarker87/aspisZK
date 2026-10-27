import RPz7_F3V_Begin
import RPz7_F3V_SemanticFinish
import RPz7_F3U_RehashPublic
import RPz7_S1SemanticCodeVerifyV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SemanticVerify
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : Hash) (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    F3U_Rehash.code H (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes hash obs)=
      S1SemanticCode.verify (S1SemanticCode.finish R B) (F3U_Rehash.dictionary H D) pub bytes hash obs := by
  simp only [S1SemanticCode.verify,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3U_RehashPublic.same, F3V_Begin.same, F3V_SemanticFinish.same,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_SemanticVerify
end
