import F3V_TranscriptAbsorb
import F3V_RehashCongr
import S1PreparedQueryEffectsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Queries
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Hash)
    (row : U8) (payload : Slice U8) :
    F3U_Rehash.code H (PreparedQueryEffects.queries effects B D self row payload)=
      PreparedQueryEffects.queries effects B (F3U_Rehash.dictionary H D) self row payload := by
  unfold PreparedQueryEffects.queries
  repeat' first
    | (solve | exact F3V_TranscriptAbsorb.same H D _ _ _)
    | (solve | rfl)
    | apply F3V_RehashCongr.bind
    | intro x
    | split

#print axioms same
end AspisR1.F3V_Queries
end
