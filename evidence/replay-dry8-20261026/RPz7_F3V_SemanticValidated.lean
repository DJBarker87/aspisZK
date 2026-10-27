import RPz7_F3U_RehashBind
import RPz7_F3V_SampleBlock
import RPz7_S1SemanticCodeSemanticValidatedV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SemanticValidated
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (self : r1_wire.SemanticTranscript Hash) (record : r1_wire.ValidatedRecord) :
    F3U_Rehash.code H (S1SemanticCode.semanticValidated D self record)=
      S1SemanticCode.semanticValidated (F3U_Rehash.dictionary H D) self record := by
  simp only [S1SemanticCode.semanticValidated,F3U_RehashBind.bind,F3U_RehashBind.lift,F3U_RehashBind.digest]
  repeat' first
    | rfl
    | exact F3V_SampleBlock.same H D _ _ _
    | (fail_if_no_progress simp only [F3U_RehashBind.bind,F3V_SampleBlock.same,PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | (apply congrArg (Code.digest _ _ _);funext x)
    | split

#print axioms same
end AspisR1.F3V_SemanticValidated
end
