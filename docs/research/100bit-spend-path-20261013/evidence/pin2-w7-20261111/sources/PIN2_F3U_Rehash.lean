import RPz7_F3U_RehashPublic
import PIN2_S1SemanticCodeVerifyV1
/-! PIN2 W9 (2026-11-11): twins of the release F3U_RehashInit.same and F3U_RehashPublic.same
for the PIN2 lifts `newTranscript` and `publicTranscript` (over `dictionaryPIN2`, the release
`F3U_Rehash.dictionary` on the PIN2 digest carrier; its frozen copy is the frozen dictionary,
`dictionaryPIN2_back`, by rfl), and the same fact for `publicTranscriptPIN2` on the frozen
carriers (`publicTranscriptPIN2_same`: the copy of the frozen dictionary is `dictionaryPIN2`
of the copy).  Each proof is the release tactic script with the PIN2 names. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PIN2_F3U_Rehash
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode

/-- `F3U_Rehash.dictionary` on the PIN2 emission's digest carrier. -/
def dictionaryPIN2 (H : Bytes → State) {Hash : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Hash) :
    AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Hash :=
  {D with digest:=fun _ parts=>F3U_Oracle.hashv H parts}

theorem dictionaryPIN2_back (H : Bytes → State) {Hash : Type} (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Hash) :
    AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack (dictionaryPIN2 H D) =
      F3U_Rehash.dictionary H (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack D) := rfl

theorem dictionaryPIN2_copy (H : Bytes → State) {Hash : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 Hash) :
    dictionaryPIN2 H (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest D) =
      AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (F3U_Rehash.dictionary H D) := rfl

/-- Twin of `F3U_RehashInit.same` for the PIN2 lift `newTranscript`. -/
theorem init_same {Hash : Type} (H : Bytes → State) (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub : Slice U8) (root : Array U8 32#usize) :
    F3U_Rehash.code H (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript D hash pub root)=
      AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript (dictionaryPIN2 H D) hash pub root := by
  simp only [AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript,F3U_RehashBind.bind,F3U_RehashBind.lift,
    F3U_RehashBind.digest]
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [AspisR1PublicPreparation.PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (Code.step _);funext x)
    | (apply congrArg (Code.digest _ _ _);funext x)
    | split

/-- Twin of `F3U_RehashPublic.same` for the PIN2 lift `publicTranscript`. -/
theorem public_same {Hash : Type} (H : Bytes → State) (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : Array U8 32#usize) :
    F3U_Rehash.code H (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript D pub hash root)=
      AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript (dictionaryPIN2 H D) pub hash root := by
  simp only [AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript,F3U_RehashBind.bind,F3U_RehashBind.lift]
  repeat' first
    | rfl
    | exact init_same H D hash _ root
    | (fail_if_no_progress simp only [AspisR1PublicPreparation.PreparedHashCode.bind,F3U_Rehash.code])
    | (apply congrArg (Code.step _);funext x)
    | split

/-- The rehash of `publicTranscriptPIN2` (frozen carriers) is `publicTranscriptPIN2` of the
frozen dictionary. -/
theorem publicTranscriptPIN2_same {Hash : Type} (H : Bytes → State) (D : AspisR1PublicPreparation.aspis_core.Digest32 Hash)
    (hash : Hash) (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : Array U8 32#usize) :
    F3U_Rehash.code H (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 D pub hash root)=
      AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 (F3U_Rehash.dictionary H D) pub hash root := by
  unfold AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2
  rw [F3U_RehashBind.bind,public_same,dictionaryPIN2_copy]
  rfl

#print axioms dictionaryPIN2_back
#print axioms dictionaryPIN2_copy
#print axioms init_same
#print axioms public_same
#print axioms publicTranscriptPIN2_same
end AspisR1.PIN2_F3U_Rehash
end
