import RPz7_F3V_SemanticVerify
import PIN2_F3U_Rehash
/-! PIN2 W9 (2026-11-11): twin of the release F3V_SemanticVerify.same for `verifyPIN2`; the
release tactic script with `verifyPIN2` and `PIN2_F3U_Rehash.publicTranscriptPIN2_same` in
place of `verify` and `F3U_RehashPublic.same`.  Conclusion as in the release. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2_F3V_SemanticVerify
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : Hash) (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    F3U_Rehash.code H (S1SemanticCode.verifyPIN2 (S1SemanticCode.finish R B) D pub bytes hash obs)=
      S1SemanticCode.verifyPIN2 (S1SemanticCode.finish R B) (F3U_Rehash.dictionary H D) pub bytes hash obs := by
  simp only [S1SemanticCode.verifyPIN2,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, PIN2_F3U_Rehash.publicTranscriptPIN2_same, F3V_Begin.same, F3V_SemanticFinish.same,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.PIN2_F3V_SemanticVerify
end
