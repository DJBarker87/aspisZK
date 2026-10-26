import F3U_RehashPublic
import F3U_RehashValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_PublicOracleValue
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem initial {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (pub : Slice U8) (root : Array U8 32#usize) :
    (eval H (oracleProgram (S1SemanticCode.newTranscript D hash pub root))).2=
      erase (S1SemanticCode.newTranscript (F3U_Rehash.dictionary H D) hash pub root) := by
  rw [F3U_RehashValue.value,F3U_RehashInit.same]

theorem public {Hash : Type} (H : Bytes → State) (D : aspis_core.Digest32 Hash)
    (hash : Hash) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : Array U8 32#usize) :
    (eval H (oracleProgram (S1SemanticCode.publicTranscript D pub hash root))).2=
      erase (S1SemanticCode.publicTranscript (F3U_Rehash.dictionary H D) pub hash root) := by
  rw [F3U_RehashValue.value,F3U_RehashPublic.same]

#print axioms initial
#print axioms public
end AspisR1.F3U_PublicOracleValue
end
