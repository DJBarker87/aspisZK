import F3V_Rounds
import F3V_CircleValidated
import S1SemanticCodeFinishV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SemanticFinish
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Hash)
    (ch : r1_wire.Challenges) (obs : Option (verifier.Phase → Result Unit)) :
    F3U_Rehash.code H (S1SemanticCode.finish R B D pub p t ch obs)=
      S1SemanticCode.finish R B (F3U_Rehash.dictionary H D) pub p t ch obs := by
  simp only [S1SemanticCode.finish,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3V_Rounds.same, F3V_CircleValidated.same,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_SemanticFinish
end
