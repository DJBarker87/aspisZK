import R1LiteralTypedWords
import R1TypedRecoveredWords
import R1FoldedRecoveredWord
import R1MerkleIndexGeometry
import R1ExactLeafFieldCodec

/-! Pointwise projection of the strict payloads recovered at common Merkle
cuts. A query cell is the zero-extended original index; the C1/C2 and folded leaf
indices have the same numeric value, and the within-leaf slot is the same modulo-four value.
-/
set_option autoImplicit false

namespace AspisR1.CanonicalCutTypedProjection

open AspisR1.TypedRecoveredWords
open AspisR1.LiteralTypedWords
open AspisR1.MixedLeafDecoder
open AspisR1.MixedLeafEncoding
open AspisR1.ExactLeafFieldCodec
open AspisR1.FoldedRecoveredWord
open AspisR1.FoldedLeafCodec
open AspisR1.MerkleIndexGeometry
open AspisPool.AlgorithmicCircleDecoderV7

/-- View a folded/query index as an original semantic-word index. -/
def queryPosition (q : Fin 262144) : Fin 1048576 :=
  ⟨q.val, by have h := q.isLt; omega⟩

theorem queryLeaf_queryPosition_val (q : Fin 262144) :
    (queryLeaf (queryPosition q)).val = (foldedIndex q).val := rfl

theorem querySlot_queryPosition (q : Fin 262144) :
    querySlot (queryPosition q) = foldedSlot q := by
  apply Fin.ext
  rfl

theorem decoded_cut_payloads_project_at
    {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (foldedPacked : Fin 65536 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (q : Fin 262144) (c1 : AspisR1.TypedRecoveredWords.C1) (c2 : AspisR1.TypedRecoveredWords.C2) (folded : AspisR1.FoldedLeafCodec.Folded)
    (hc1 : AspisR1.TypedRecoveredWords.decodeC1At c1Packed (queryLeaf (queryPosition q)) = some c1)
    (hc2 : AspisR1.TypedRecoveredWords.decodeC2At c2Packed (queryLeaf (queryPosition q)) = some c2)
    (hfolded : (foldedPacked (foldedIndex q)).bind
      AspisR1.FoldedLeafCodec.decodeFolded = some folded) :
    (∀ l : Fin 26,
      TypedRecoveredWords.word eM eK c1Packed c2Packed
        ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) =
          eM ((c1 (querySlot (queryPosition q))).1 l)) ∧
    TypedRecoveredWords.word eM eK c1Packed c2Packed ⟨26, by decide⟩ (queryPosition q) =
      eK ((c2 (querySlot (queryPosition q))) ⟨0, by decide⟩) ∧
    TypedRecoveredWords.word eM eK c1Packed c2Packed ⟨27, by decide⟩ (queryPosition q) =
      eK ((c2 (querySlot (queryPosition q))) ⟨1, by decide⟩) ∧
    TypedRecoveredWords.word eM eK c1Packed c2Packed ⟨28, by decide⟩ (queryPosition q) =
      eK ((c1 (querySlot (queryPosition q))).2) ∧
    FoldedRecoveredWord.wordOfPacked (foldedPacked (foldedIndex q)) q =
      folded (foldedSlot q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l
    exact TypedRecoveredWords.word_c1_base_of_decode eM eK c1Packed c2Packed
      (queryPosition q) l c1 hc1
  · exact TypedRecoveredWords.word_c2_first_of_decode eM eK c1Packed c2Packed
        (queryPosition q) c2 hc2
  · exact TypedRecoveredWords.word_c2_second_of_decode eM eK c1Packed c2Packed
        (queryPosition q) c2 hc2
  · exact TypedRecoveredWords.word_c1_tail_of_decode eM eK c1Packed c2Packed
        (queryPosition q) c1 hc1
  · have hsuccess : ∃ bytes,
        foldedPacked (foldedIndex q) = some bytes ∧
          AspisR1.FoldedLeafCodec.decodeFolded bytes = some folded := by
      cases hp : foldedPacked (foldedIndex q) with
      | none => simp [hp] at hfolded
      | some bytes => exact ⟨bytes, rfl, by simpa [hp] using hfolded⟩
    rcases hsuccess with ⟨bytes, hbytes, hdecoded⟩
    exact FoldedRecoveredWord.wordOfPacked_success _ bytes folded q hbytes hdecoded


/-- The same pointwise conclusions, phrased for `LiteralTypedWords.word`.
The C1/C2 words here are exactly the commitment-time decoders' total
zero-default values, via the established definitional recovery bridge. -/
theorem literal_word_from_cut_payloads_at
    {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (foldedPacked : Fin 65536 → Option (List AspisR1.ExactLeafFieldCodec.Byte))
    (q : Fin 262144) (c1 : AspisR1.TypedRecoveredWords.C1)
    (c2 : AspisR1.TypedRecoveredWords.C2) (folded : AspisR1.FoldedLeafCodec.Folded)
    (hc1 : AspisR1.TypedRecoveredWords.decodeC1At c1Packed
      (queryLeaf (queryPosition q)) = some c1)
    (hc2 : AspisR1.TypedRecoveredWords.decodeC2At c2Packed
      (queryLeaf (queryPosition q)) = some c2)
    (hfolded : (foldedPacked (foldedIndex q)).bind
      AspisR1.FoldedLeafCodec.decodeFolded = some folded) :
    (∀ l : Fin 26,
      LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value c1Packed)
        (TypedRecoveredWords.c2Value c2Packed)
        ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) =
          eM ((c1 (querySlot (queryPosition q))).1 l)) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value c1Packed)
      (TypedRecoveredWords.c2Value c2Packed) ⟨26, by decide⟩ (queryPosition q) =
        eK ((c2 (querySlot (queryPosition q))) ⟨0, by decide⟩) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value c1Packed)
      (TypedRecoveredWords.c2Value c2Packed) ⟨27, by decide⟩ (queryPosition q) =
        eK ((c2 (querySlot (queryPosition q))) ⟨1, by decide⟩) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value c1Packed)
      (TypedRecoveredWords.c2Value c2Packed) ⟨28, by decide⟩ (queryPosition q) =
        eK ((c1 (querySlot (queryPosition q))).2) ∧
    FoldedRecoveredWord.wordOfPacked (foldedPacked (foldedIndex q)) q =
      folded (foldedSlot q) := by
  simpa only [LiteralTypedWords.word_recovered_eq] using
    (decoded_cut_payloads_project_at eM eK c1Packed c2Packed foldedPacked
      q c1 c2 folded hc1 hc2 hfolded)

#print axioms literal_word_from_cut_payloads_at

#print axioms queryLeaf_queryPosition_val
#print axioms querySlot_queryPosition
#print axioms decoded_cut_payloads_project_at

end AspisR1.CanonicalCutTypedProjection
