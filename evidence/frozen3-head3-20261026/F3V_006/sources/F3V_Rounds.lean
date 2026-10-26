import F3V_RoundStep
import S1SemanticCodeRoundsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Rounds
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (B : RoundModel.Boundaries) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Hash) :
    F3U_Rehash.code H (S1SemanticCode.rounds B D p t)=
      S1SemanticCode.rounds B (F3U_Rehash.dictionary H D) p t := by
  simp only [S1SemanticCode.rounds,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3V_RoundStep.same,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_Rounds
end
