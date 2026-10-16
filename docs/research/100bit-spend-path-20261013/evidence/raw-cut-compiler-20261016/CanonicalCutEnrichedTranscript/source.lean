import R1CanonicalCutWordProjection
import R1CanonicalCutTypedProjection
import R1LiteralTranscript
import R1TypedRecoveredWords
import R1FoldedRecoveredWord
import R1MerkleIndexGeometry
import R1LiteralTypedWords
import RawByteCutStability
import R1PublicInitFrame
import R1CommitmentRootFrames

/-! An ideal literal transcript whose auxiliary word metadata is constructed
from the commitment-cut packed maps. Erased transcript messages, public
statement, and challenges are preserved exactly. This does not assert that
arbitrary pre-existing metadata equals the cut-derived words. -/
set_option autoImplicit false

namespace AspisR1.CanonicalCutEnrichedTranscript

open AspisR1.TypedRecoveredWords
open AspisR1.FoldedRecoveredWord
open AspisR1.MerkleIndexGeometry
open AspisR1.LiteralTranscript
open AspisPool.AlgorithmicCircleDecoderV7
open FS FS2 FS2.Duplex AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open Merkle32Path

abbrev Byte := AspisR1.ExactLeafFieldCodec.Byte
abbrev E := AspisWideTower.WideExact

structure Words where
  c1 : LiteralTranscript.C1Word
  c2 : LiteralTranscript.C2Word
  final : LiteralTranscript.VWord

/-- Build all three typed words directly from the packed maps at their
commitment cuts, with the same zero-default behavior as the typed readers. -/
def wordsFromMaps
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (foldedPacked : Fin 65536 → Option (List Byte)) : Words where
  c1 := TypedRecoveredWords.c1Value c1Packed
  c2 := TypedRecoveredWords.c2Value c2Packed
  final := fun q => FoldedRecoveredWord.wordOfPacked
    (foldedPacked (MerkleIndexGeometry.foldedIndex q)) q

/-- Raw-log recovery maps for the three fixed commitment frames. The path
geometry is six base-8 levels and the packed leaf values are the recovered
first components. These are concrete map definitions only; recovery at a
particular leaf is established by `RawByteCutRecovery`/`RawByteCutStability`. -/
def rawC1Map (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0x71 480
    (RawByteCutRecovery.cut tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def rawC2Map (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0xf1 128
    (RawByteCutRecovery.cut tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def rawFoldedMap (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0x72 128
    (RawByteCutRecovery.cut tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

/-- The ideal typed words are assembled from the recovered maps at the three
actual commitment cuts. The concrete frames are caller-provided here so the
source-level frame constructors can be instantiated without adding length
premises to the recovery API. -/
def wordsFromRawCuts (tr : List (Bytes × State))
    (c1Frame c2Frame foldedFrame : Bytes) (c1Root c2Root foldedRoot : State) : Words :=
  wordsFromMaps (rawC1Map tr c1Frame c1Root) (rawC2Map tr c2Frame c2Root)
    (rawFoldedMap tr foldedFrame foldedRoot)

/-- The concrete literal commitment-frame shapes. The caller supplies the
public bytes, prefix states, roots and folded tail already selected by the
transcript; this definition only instantiates the retained frame constructors. -/
def wordsFromCommitmentFrames (tr : List (Bytes × State))
    (pubBytes : Bytes) (c1Root c2State c2Root foldedState foldedRoot : State)
    (foldedTail : Bytes) : Words :=
  wordsFromRawCuts tr
    (PublicInitFrame.pre pubBytes ++ AspisV8R19.SourceDuplexStep.bytes c1Root)
    (CommitmentRootFrames.c2Frame c2State c2Root)
    (CommitmentRootFrames.foldedFrame foldedState foldedRoot foldedTail)
    c1Root c2Root foldedRoot

/-- Full-log packed maps for comparison with the first-read cut maps. -/
def fullC1Map (tr : List (Bytes × State)) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0x71 480 tr
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def fullC2Map (tr : List (Bytes × State)) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0xf1 128 tr
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def fullFoldedMap (tr : List (Bytes × State)) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (RawByteCutStability.recoverAt 0x72 128 tr
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

/-- One raw-byte collision exclusion makes the C1, C2, and folded packed maps
at their commitment frames equal to the corresponding full-log maps. -/
theorem wordsFromRawCuts_eq_full
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (c1Frame c2Frame foldedFrame : Bytes)
    (c1Root c2Root foldedRoot : State)
    (j1 j2 j3 : Fin 11)
    (hc1frame : Read tr c1Frame)
    (hc2frame : Read tr c2Frame)
    (hfoldedframe : Read tr foldedFrame)
    (hc1pred : RawByteCollisionTargets.pred j1 c1Frame = some c1Root)
    (hc2pred : RawByteCollisionTargets.pred j2 c2Frame = some c2Root)
    (hfoldedpred : RawByteCollisionTargets.pred j3 foldedFrame = some foldedRoot) :
    wordsFromRawCuts tr c1Frame c2Frame foldedFrame c1Root c2Root foldedRoot =
      wordsFromMaps (fullC1Map tr c1Root) (fullC2Map tr c2Root)
        (fullFoldedMap tr foldedRoot) := by
  have hc1 := RawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x71 480 c1Root c1Frame j1 hc1frame hc1pred
  have hc2 := RawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0xf1 128 c2Root c2Frame j2 hc2frame hc2pred
  have hfolded := RawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x72 128 foldedRoot foldedFrame j3 hfoldedframe hfoldedpred
  have hc1map : rawC1Map tr c1Frame c1Root = fullC1Map tr c1Root := by
    funext leaf
    unfold rawC1Map fullC1Map
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hc1 (MerkleIndexGeometry.slots 6 leaf.val))
  have hc2map : rawC2Map tr c2Frame c2Root = fullC2Map tr c2Root := by
    funext leaf
    unfold rawC2Map fullC2Map
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hc2 (MerkleIndexGeometry.slots 6 leaf.val))
  have hfoldedmap : rawFoldedMap tr foldedFrame foldedRoot = fullFoldedMap tr foldedRoot := by
    funext leaf
    unfold rawFoldedMap fullFoldedMap
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hfolded (MerkleIndexGeometry.slots 6 leaf.val))
  simp [wordsFromRawCuts, hc1map, hc2map, hfoldedmap]

/-- Replace only the auxiliary typed word carried by a literal message. Raw
byte payloads and the initial commitment root are unchanged. -/
def enrichMessage (w : Words) : LiteralTranscript.Message → LiteralTranscript.Message
  | .initial root _ => .initial root w.c1
  | .payload bytes => .payload bytes
  | .c2 bytes _ => .c2 bytes w.c2
  | .second bytes _ => .second bytes w.final

def enrichRounds (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :=
  rs.map fun mc => (enrichMessage w mc.1, mc.2)

def enrichPrefix (w : Words) (P : LiteralTranscript.Prefix) : LiteralTranscript.Prefix :=
  ⟨P.statement, enrichRounds w P.rounds⟩

def enrichTranscript (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :=
  enrichRounds w rs

@[simp] theorem erase_enrichMessage (w : Words) (m : LiteralTranscript.Message) :
    LiteralTranscript.erase (enrichMessage w m) = LiteralTranscript.erase m := by
  cases m <;> rfl

theorem erase_enrichRounds (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    (enrichRounds w rs).map (fun mc => (LiteralTranscript.erase mc.1, mc.2)) =
      rs.map (fun mc => (LiteralTranscript.erase mc.1, mc.2)) := by
  induction rs with
  | nil => rfl
  | cons mc rest ih => cases mc with | mk m c => simp [enrichRounds, ih]

theorem erasePrefix_enrich (w : Words) (P : LiteralTranscript.Prefix) :
    LiteralTranscript.erasePrefix (enrichPrefix w P) = LiteralTranscript.erasePrefix P := by
  cases P with
  | mk statement rounds =>
      simp [enrichPrefix, LiteralTranscript.erasePrefix, erase_enrichRounds]

theorem sampler_enrich_eq (i : Nat) (w : Words)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    LiteralTranscript.samp i (enrichPrefix w P) (enrichMessage w m) =
      LiteralTranscript.samp i P m := by
  have hp := erasePrefix_enrich w P
  have hm := erase_enrichMessage w m
  simp only [LiteralTranscript.samp, hp, hm]

/-- The literal typed word exposed by the constructed metadata is the
commitment-map word, not a caller-supplied equality to an existing word. -/
theorem enriched_word_eq_cut_map_word
    (eM : AspisR1.ExactLeafFieldCodec.M31Exact →+* E)
    (eK : AspisR1.ExactLeafFieldCodec.QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (foldedPacked : Fin 65536 → Option (List Byte)) :
    LiteralTypedWords.word eM eK (wordsFromMaps c1Packed c2Packed foldedPacked).c1
      (wordsFromMaps c1Packed c2Packed foldedPacked).c2 =
      TypedRecoveredWords.word eM eK c1Packed c2Packed := by
  exact LiteralTypedWords.word_recovered_eq eM eK c1Packed c2Packed

/-- The newly constructed transcript metadata has the per-query opening
projections proved from the checked commitment-cut decodes. -/
theorem enriched_cut_word_projects_opening_at
    {L : Nat} (eM : AspisR1.ExactLeafFieldCodec.M31Exact →+* E)
    (eK : AspisR1.ExactLeafFieldCodec.QM31Exact →+* E)
    (representedC1 representedC2 representedFolded :
      List (FS2.Duplex.Addr L × AspisV8R19.SourceDuplexStep.State))
    (rootC1 rootC2 rootFolded : AspisV8R19.SourceDuplexStep.State)
    (q : Fin 262144)
    (c1 : AspisR1.TypedRecoveredWords.C1)
    (c2 : AspisR1.TypedRecoveredWords.C2)
    (folded : AspisR1.FoldedLeafCodec.Folded)
    (hc1 : TypedRecoveredWords.decodeC1At
      (CanonicalCutWordProjection.c1Map representedC1 rootC1)
      (AspisR1.TypedRecoveredWords.queryLeaf
        (CanonicalCutTypedProjection.queryPosition q)) = some c1)
    (hc2 : TypedRecoveredWords.decodeC2At
      (CanonicalCutWordProjection.c2Map representedC2 rootC2)
      (AspisR1.TypedRecoveredWords.queryLeaf
        (CanonicalCutTypedProjection.queryPosition q)) = some c2)
    (hfolded : (CanonicalCutWordProjection.foldedMap representedFolded rootFolded
      (MerkleIndexGeometry.foldedIndex q)).bind
        AspisR1.FoldedLeafCodec.decodeFolded = some folded) :
    (∀ l : Fin 26,
      LiteralTypedWords.word eM eK
        (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
          (CanonicalCutWordProjection.c2Map representedC2 rootC2)
          (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c1
        (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
          (CanonicalCutWordProjection.c2Map representedC2 rootC2)
          (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c2
        ⟨l.val, by have hl := l.isLt; omega⟩
        (CanonicalCutTypedProjection.queryPosition q) =
        eM ((c1 (AspisR1.TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))).1 l)) ∧
    LiteralTypedWords.word eM eK
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c1
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c2
      ⟨26, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c2 (AspisR1.TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨0, by decide⟩) ∧
    LiteralTypedWords.word eM eK
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c1
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c2
      ⟨27, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c2 (AspisR1.TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))) ⟨1, by decide⟩) ∧
    LiteralTypedWords.word eM eK
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c1
      (wordsFromMaps (CanonicalCutWordProjection.c1Map representedC1 rootC1)
        (CanonicalCutWordProjection.c2Map representedC2 rootC2)
        (CanonicalCutWordProjection.foldedMap representedFolded rootFolded)).c2
      ⟨28, by decide⟩ (CanonicalCutTypedProjection.queryPosition q) =
        eK ((c1 (AspisR1.TypedRecoveredWords.querySlot
          (CanonicalCutTypedProjection.queryPosition q))).2) ∧
    FoldedRecoveredWord.wordOfPacked
      (CanonicalCutWordProjection.foldedMap representedFolded rootFolded
        (MerkleIndexGeometry.foldedIndex q)) q =
      folded (FoldedRecoveredWord.foldedSlot q) := by
  -- The helper's word is constructed from exactly these cut-map projections.
  simpa [wordsFromMaps] using
    (CanonicalCutWordProjection.commitment_cut_word_projects_opening_at
      eM eK representedC1 representedC2 representedFolded rootC1 rootC2 rootFolded
      q c1 c2 folded hc1 hc2 hfolded)

#print axioms enriched_cut_word_projects_opening_at

#print axioms erase_enrichMessage
#print axioms erase_enrichRounds
#print axioms erasePrefix_enrich
#print axioms sampler_enrich_eq
#print axioms enriched_word_eq_cut_map_word

end AspisR1.CanonicalCutEnrichedTranscript
