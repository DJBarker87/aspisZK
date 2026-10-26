import F3V_TranscriptBlock
import S1PreparedScalarEffectsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Rho
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (B : PreparedModel.Boundaries) (self : transcript.Transcript Hash)
    (row : U8) (payload : Slice U8) :
    F3U_Rehash.code H (PreparedScalarEffects.scalar_k effects B D self row payload)=
      PreparedScalarEffects.scalar_k effects B (F3U_Rehash.dictionary H D) self row payload := by
  simp only [PreparedScalarEffects.scalar_k,F3U_RehashBind.bind,F3U_RehashBind.lift,
    F3V_TranscriptBlock.same]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_Rho
end
