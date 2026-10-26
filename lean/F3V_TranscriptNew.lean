import F3U_RehashBind
import S1PreparedHashErasureV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_TranscriptNew
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (state : Array U8 32#usize) (variant : transport.Variant) :
    F3U_Rehash.code H (PreparedHashEffects.new effects D hash state variant)=
      PreparedHashEffects.new effects (F3U_Rehash.dictionary H D) hash state variant := by
  simp only [PreparedHashEffects.new,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [F3U_RehashBind.bind, F3U_RehashBind.digest,  PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3V_TranscriptNew
end
