import F3U_RehashBind
import S1SemanticCodeSampleBlockV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SampleBlock
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (self : r1_wire.SemanticTranscript Hash) (row : U8) (framed : Slice U8) :
    F3U_Rehash.code H (S1SemanticCode.sampleBlock D self row framed)=
      S1SemanticCode.sampleBlock (F3U_Rehash.dictionary H D) self row framed := by
  simp only [S1SemanticCode.sampleBlock,F3U_RehashBind.bind,F3U_RehashBind.lift,F3U_RehashBind.digest]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (Code.step _);funext x)
    | (apply congrArg (Code.digest _ _ _);funext x)
    | split

#print axioms same
end AspisR1.F3V_SampleBlock
end
