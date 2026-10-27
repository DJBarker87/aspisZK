import RPz7_F3V_Begin5
import RPz7_S1SemanticCodeBeginV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Begin
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript Hash) :
    F3U_Rehash.code H (S1SemanticCode.begin D p t)=
      S1SemanticCode.begin (F3U_Rehash.dictionary H D) p t := by
  simp only [S1SemanticCode.begin,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3V_SemanticValidated.same, F3V_Begin5.same,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_Begin
end
