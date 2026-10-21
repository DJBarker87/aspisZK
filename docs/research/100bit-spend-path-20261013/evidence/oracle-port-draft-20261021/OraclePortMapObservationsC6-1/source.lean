import OraclePortObservationTransportC6
import OraclePortPackedChoiceC4

/-! Lift indexed packed-byte agreement through the total decoders to exactly
the selected word fibres consumed by the observation checker. Invalid leaves
use the same zero defaults on both sides; no global map equality is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortMapObservationsC6
open LiteralAcceptanceTerminal AspisV8R19.DuplexFrames
open CanonicalCutEnrichedTranscript
attribute [local irreducible] MixedLeafDecoder.decodeC1 MixedLeafDecoder.decodeC2 FoldedLeafCodec.decodeFolded

theorem queryLeaf_child (u : Fin 262144) (slot : Fin 4) :
    TypedRecoveredWords.queryLeaf (childIndex u slot) = u := by
  apply Fin.ext
  simp only [TypedRecoveredWords.queryLeaf,childIndex]
  have h := slot.isLt
  omega

theorem folded_parent (u : Fin 262144) : MerkleIndexGeometry.foldedIndex u = parentIndex u := rfl

theorem folded_child (u : Fin 65536) (slot : Fin 4) :
    MerkleIndexGeometry.foldedIndex (childIndex u slot) = u := by
  apply Fin.ext
  simp only [MerkleIndexGeometry.foldedIndex,childIndex]
  have h := slot.isLt
  omega

theorem initial_fibres
    (a b a' b' : Fin 262144 → Option Bytes)
    (q : Fin 22 → Fin 262144)
    (ha : ∀ j, a (q j) = a' (q j)) (hb : ∀ j, b (q j) = b' (q j)) :
    ∀ j lane,
      FirstFold.fibre (LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
        (wordsFromMaps a b (fun _ => none)).c1 (wordsFromMaps a b (fun _ => none)).c2 lane) (q j) =
      FirstFold.fibre (LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
        (wordsFromMaps a' b' (fun _ => none)).c1 (wordsFromMaps a' b' (fun _ => none)).c2 lane) (q j) := by
  intro j lane
  funext slot
  simp only [FirstFold.fibre,LiteralTypedWords.word,wordsFromMaps,
    TypedRecoveredWords.c1Value,TypedRecoveredWords.c2Value,
    TypedRecoveredWords.decodeC1At,TypedRecoveredWords.decodeC2At,queryLeaf_child,ha,hb]

theorem final_selected
    (a b : Fin 262144 → Option Bytes) (v v' : Fin 65536 → Option Bytes)
    (q : Fin 22 → Fin 262144) (same : ∀ j, v (parentIndex (q j)) = v' (parentIndex (q j))) :
    (∀ j, (wordsFromMaps a b v).final (q j) = (wordsFromMaps a b v').final (q j)) ∧
    (∀ j slot, (wordsFromMaps a b v).final (childIndex (parentIndex (q j)) slot) =
      (wordsFromMaps a b v').final (childIndex (parentIndex (q j)) slot)) := by
  constructor
  · intro j
    simp only [wordsFromMaps,folded_parent,same]
  · intro j slot
    simp only [wordsFromMaps,folded_child,same]

/-- Authentication at selected indices gives map agreement even if the first
occurrence lies in the other TX batch. The compiler can retain extra leaves. -/
theorem packed_selected (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (raw : Nat → Option Bytes) (kind : Nat)
    (authenticated : ∀ pos, pos < 22 → raw (OraclePortSelectedDraft.index q kind pos) =
      some (OraclePortPackedChoiceC4.payload p kind pos)) :
    ∀ j : Fin 22,
      OraclePortStoredDecisionDraftC4.packed p q kind (OraclePortSelectedDraft.index q kind j.val) =
        raw (OraclePortSelectedDraft.index q kind j.val) := by
  intro j
  exact OraclePortPackedChoiceC4.packed_agrees p q kind raw authenticated j.val j.isLt

#print axioms queryLeaf_child
#print axioms folded_parent
#print axioms folded_child
#print axioms initial_fibres
#print axioms final_selected
#print axioms packed_selected
end AspisR1.OraclePortMapObservationsC6
end
