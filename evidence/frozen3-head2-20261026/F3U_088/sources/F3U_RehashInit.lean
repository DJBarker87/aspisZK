import F3U_RehashBind
import S1SemanticCodeNewTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RehashInit
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (pub : Slice U8) (root : Array U8 32#usize) :
    F3U_Rehash.code H (S1SemanticCode.newTranscript D hash pub root)=
      S1SemanticCode.newTranscript (F3U_Rehash.dictionary H D) hash pub root := by
  simp only [S1SemanticCode.newTranscript,F3U_RehashBind.bind,F3U_RehashBind.lift,F3U_RehashBind.digest]
  rfl

#print axioms same
end AspisR1.F3U_RehashInit
end
