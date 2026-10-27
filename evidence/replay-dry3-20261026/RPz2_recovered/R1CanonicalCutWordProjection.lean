import R1CanonicalCutOpening
import R1CanonicalCutTypedProjection
import R1LiteralTypedWords
import R1ExactLeafFieldCodec
import R1TypedRecoveryStability
import R1FoldedRecoveredWord
import R1CanonicalTypedOpening
import R1MerkleIndexGeometry

/-! Construct the typed literal word from the three commitment-time packed
maps, then project strict opening payloads through it. The decode facts below
are exactly outputs of `CanonicalCutOpening` at each corresponding cut. -/
set_option autoImplicit false

namespace AspisR1.CanonicalCutWordProjection

open AspisR1.TypedRecoveredWords
open AspisR1.CanonicalTypedOpening
open AspisR1.TypedRecoveryStability
open AspisR1.FoldedRecoveredWord
open AspisR1.MerkleIndexGeometry
open AspisR1.ExactLeafFieldCodec
open AspisPool.AlgorithmicCircleDecoderV7

abbrev Byte := AspisR1.ExactLeafFieldCodec.Byte

variable {L : Nat}

/-- Commitment-cut C1 and C2 maps are the packed maps used by the typed
recovery projection. -/
def c1Map (represented : List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State))
    (root : AspisV8R19.SourceDuplexStep.State) : Fin 262144 → Option (List Byte) :=
  TypedRecoveryStability.c1PackedAt represented CanonicalTypedOpening.paths6C1C2 root

def c2Map (represented : List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State))
    (root : AspisV8R19.SourceDuplexStep.State) : Fin 262144 → Option (List Byte) :=
  TypedRecoveryStability.c2PackedAt represented CanonicalTypedOpening.paths6C1C2 root

def foldedMap (represented : List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State))
    (root : AspisV8R19.SourceDuplexStep.State) : Fin 65536 → Option (List Byte) :=
  fun leaf => FoldedRecoveredWord.packedAt represented root leaf

/-- At every queried position, the word defined by commitment-cut C1/C2 maps
has the exact C1/C2 slot values of the strict opening payloads; the folded
commitment map yields the corresponding folded slot. The three decode
premises are the conclusions of the checked C1, C2 and folded cut theorems. -/
theorem commitment_cut_word_projects_opening_at
    {E : Type} [Field E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (representedC1 representedC2 representedFolded :
      List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State))
    (rootC1 rootC2 rootFolded : AspisV8R19.SourceDuplexStep.State)
    (q : Fin 262144)
    (c1 : AspisR1.TypedRecoveredWords.C1)
    (c2 : AspisR1.TypedRecoveredWords.C2)
    (folded : AspisR1.FoldedLeafCodec.Folded)
    (hc1 : TypedRecoveredWords.decodeC1At (c1Map representedC1 rootC1)
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)) = some c1)
    (hc2 : TypedRecoveredWords.decodeC2At (c2Map representedC2 rootC2)
      (queryLeaf (CanonicalCutTypedProjection.queryPosition q)) = some c2)
    (hfolded : (foldedMap representedFolded rootFolded (foldedIndex q)).bind
      AspisR1.FoldedLeafCodec.decodeFolded = some folded) :
    (∀ l : Fin 26,
      LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value (c1Map representedC1 rootC1))
        (TypedRecoveredWords.c2Value (c2Map representedC2 rootC2))
        ⟨l.val, by have hl := l.isLt; omega⟩
        (CanonicalCutTypedProjection.queryPosition q) =
          eM ((c1 (TypedRecoveredWords.querySlot
            (CanonicalCutTypedProjection.queryPosition q))).1 l)) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value (c1Map representedC1 rootC1))
      (TypedRecoveredWords.c2Value (c2Map representedC2 rootC2)) ⟨26, by decide⟩
      (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c2 (TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨0, by decide⟩) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value (c1Map representedC1 rootC1))
      (TypedRecoveredWords.c2Value (c2Map representedC2 rootC2)) ⟨27, by decide⟩
      (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c2 (TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨1, by decide⟩) ∧
    LiteralTypedWords.word eM eK (TypedRecoveredWords.c1Value (c1Map representedC1 rootC1))
      (TypedRecoveredWords.c2Value (c2Map representedC2 rootC2)) ⟨28, by decide⟩
      (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c1 (TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))).2) ∧
    FoldedRecoveredWord.wordOfPacked (foldedMap representedFolded rootFolded (foldedIndex q)) q =
      folded (FoldedRecoveredWord.foldedSlot q) := by
  exact CanonicalCutTypedProjection.literal_word_from_cut_payloads_at
    eM eK (c1Map representedC1 rootC1) (c2Map representedC2 rootC2)
    (foldedMap representedFolded rootFolded) q c1 c2 folded hc1 hc2 hfolded

#print axioms commitment_cut_word_projects_opening_at

end AspisR1.CanonicalCutWordProjection
