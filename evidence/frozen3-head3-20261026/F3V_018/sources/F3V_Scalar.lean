import F3V_TranscriptBlock
import S1PreparedScalarEffectsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Scalar
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (B : PreparedModel.Boundaries) (self : transcript.Transcript Hash)
    (row : U8) (payload : Slice U8) (nonzero : Bool) :
    F3U_Rehash.code H (PreparedScalarEffects.scalar effects B D self row payload nonzero)=
      PreparedScalarEffects.scalar effects B (F3U_Rehash.dictionary H D) self row payload nonzero := by
  simp only [PreparedScalarEffects.scalar,F3U_RehashBind.bind,F3U_RehashBind.lift,
    F3V_TranscriptBlock.same]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_Scalar
end
