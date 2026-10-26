import RPz7_F3V_TranscriptNew
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_TranscriptAbsorb
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (self : transcript.Transcript Hash) (row : U8) (payload : Slice U8) :
    F3U_Rehash.code H (PreparedHashEffects.absorb effects D self row payload)=
      PreparedHashEffects.absorb effects (F3U_Rehash.dictionary H D) self row payload := by
  simp only [PreparedHashEffects.absorb,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3U_RehashBind.digest,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_TranscriptAbsorb
end
