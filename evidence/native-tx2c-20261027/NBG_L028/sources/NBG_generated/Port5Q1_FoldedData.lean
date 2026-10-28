import Port5Q1_Parsed
import R1FoldedRecoveredWord
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_FoldedData
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
abbrev FE := AspisWideTower.WideExact
attribute [local irreducible] FoldedLeafCodec.decodeFolded CanonicalCutEnrichedTranscript.wordsFromMaps

theorem quartet (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (data : MatchingSupport.Data FE)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (j : Fin 22) (values : Fin 4 → FE)
    (decoded : FoldedLeafCodec.decodeFolded (slice (opening parsed j.val) 672 128)=some values) :
    ∀ t, values t=data.V (AspisR1.childIndex (AspisR1.parentIndex (n:=65536) (q j)) t) := by
  intro t
  rw [Port5Q1_Parsed.data_word parsed q tr data read]
  let parent := AspisR1.parentIndex (n:=65536) (q j)
  have leaf : MerkleIndexGeometry.foldedIndex (AspisR1.childIndex parent t)=parent := by
    apply Fin.ext
    change (4*parent.val+t.val)/4=parent.val
    have := t.isLt
    omega
  have slot : FoldedRecoveredWord.foldedSlot (AspisR1.childIndex parent t)=t := by
    apply Fin.ext
    change (4*parent.val+t.val)%4=t.val
    have := t.isLt
    omega
  unfold words CanonicalCutEnrichedTranscript.wordsFromMaps
  change values t=FoldedRecoveredWord.wordOfPacked
    (packed parsed q 2 (MerkleIndexGeometry.foldedIndex (AspisR1.childIndex parent t)).val)
    (AspisR1.childIndex parent t)
  rw [leaf]
  rw [FoldedRecoveredWord.wordOfPacked_success _ _ values _
    (Port5Q1_Parsed.packed_at parsed q recovered authenticated j) decoded,slot]

#print axioms quartet
end AspisR1.Port5Q1_FoldedData
end
