import OraclePortLeafRecovery

/-! Packed-leaf equality is sufficient for selected typed slots, including
failed strict decodes (both sides use the same zero default). It does not
assert equality of the full words at unselected coordinates. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortTypedSlotsDraft
open AspisV8R19.DuplexFrames
open CanonicalCutEnrichedTranscript

abbrev Packed := Fin 262144 → Option Bytes
abbrev FoldedPacked := Fin 65536 → Option Bytes

theorem c1_slot (left right : Packed) (i : Fin 1048576)
    (same : left (TypedRecoveredWords.queryLeaf i) = right (TypedRecoveredWords.queryLeaf i)) :
    TypedRecoveredWords.c1Value left i = TypedRecoveredWords.c1Value right i := by
  unfold TypedRecoveredWords.c1Value TypedRecoveredWords.decodeC1At
  rw [same]

theorem c2_slot (left right : Packed) (i : Fin 1048576)
    (same : left (TypedRecoveredWords.queryLeaf i) = right (TypedRecoveredWords.queryLeaf i)) :
    TypedRecoveredWords.c2Value left i = TypedRecoveredWords.c2Value right i := by
  unfold TypedRecoveredWords.c2Value TypedRecoveredWords.decodeC2At
  rw [same]

theorem folded_slot (left right : FoldedPacked) (i : Fin 262144)
    (same : left (MerkleIndexGeometry.foldedIndex i) = right (MerkleIndexGeometry.foldedIndex i)) :
    (wordsFromMaps (fun _ => none) (fun _ => none) left).final i =
      (wordsFromMaps (fun _ => none) (fun _ => none) right).final i := by
  change FoldedRecoveredWord.wordOfPacked _ i = FoldedRecoveredWord.wordOfPacked _ i
  rw [same]

/-- Selected C1/C2 bytes transfer through all 29 typed lane projections. -/
theorem lanes {E : Type} [Field E]
    (eM : ExactLeafFieldCodec.M31Exact →+* E) (eK : ExactLeafFieldCodec.QM31Exact →+* E)
    (c1 d1 c2 d2 : Packed) (i : Fin 1048576)
    (h1 : c1 (TypedRecoveredWords.queryLeaf i) = d1 (TypedRecoveredWords.queryLeaf i))
    (h2 : c2 (TypedRecoveredWords.queryLeaf i) = d2 (TypedRecoveredWords.queryLeaf i))
    (lane : Fin 29) :
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value c1) (TypedRecoveredWords.c2Value c2) lane i =
      LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value d1) (TypedRecoveredWords.c2Value d2) lane i := by
  unfold LiteralTypedWords.word
  rw [c1_slot c1 d1 i h1,c2_slot c2 d2 i h2]

/-- There is no use of funext over an unqueried domain in the transfer. -/
theorem selected_slots (c1 d1 c2 d2 : Packed) (v w : FoldedPacked)
    (selected : List (Fin 1048576)) (finalSelected : List (Fin 262144))
    (h1 : ∀ i ∈ selected, c1 (TypedRecoveredWords.queryLeaf i) = d1 (TypedRecoveredWords.queryLeaf i))
    (h2 : ∀ i ∈ selected, c2 (TypedRecoveredWords.queryLeaf i) = d2 (TypedRecoveredWords.queryLeaf i))
    (hv : ∀ i ∈ finalSelected, v (MerkleIndexGeometry.foldedIndex i) = w (MerkleIndexGeometry.foldedIndex i)) :
    (∀ i ∈ selected, (wordsFromMaps c1 c2 v).c1 i = (wordsFromMaps d1 d2 w).c1 i ∧
      (wordsFromMaps c1 c2 v).c2 i = (wordsFromMaps d1 d2 w).c2 i) ∧
    (∀ i ∈ finalSelected, (wordsFromMaps c1 c2 v).final i = (wordsFromMaps d1 d2 w).final i) := by
  constructor
  · intro i hi
    exact ⟨c1_slot c1 d1 i (h1 i hi),c2_slot c2 d2 i (h2 i hi)⟩
  · intro i hi
    exact folded_slot v w i (hv i hi)

#print axioms c1_slot
#print axioms c2_slot
#print axioms folded_slot
#print axioms lanes
#print axioms selected_slots
end AspisR1.OraclePortTypedSlotsDraft
end
