import F3U_RehashInit
import S1SemanticCodePublicTranscriptV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RehashPublic
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize) :
    F3U_Rehash.code H (S1SemanticCode.publicTranscript D pub hash root)=
      S1SemanticCode.publicTranscript (F3U_Rehash.dictionary H D) pub hash root := by
  simp only [S1SemanticCode.publicTranscript,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | exact F3U_RehashInit.same H D hash _ root
    | (fail_if_no_progress simp only [PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (Code.step _);funext x)
    | split

#print axioms same
end AspisR1.F3U_RehashPublic
end
