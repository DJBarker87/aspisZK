import BinThreeCommitmentTypedOpening

/-! Binary C1 and folded words, with exact first-read cuts. Source adapters
supply the actual read and parsed-target gates; no coordinate union. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinSourceCommitmentWords
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open BinCanonicalCutWords

def c1Word (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    LiteralTranscript.C1Word := TypedRecoveredWords.c1Value (rawC1Map tr frame root)

def foldedWord (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    LiteralTranscript.VWord := fun q => FoldedRecoveredWord.wordOfPacked
      (rawFoldedMap tr frame root (MerkleIndexGeometry.foldedIndex q)) q

theorem c1_word_stable
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (root : State) (frame : Bytes) (j : Fin 5) (hread : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    : rawC1Map tr frame root = fullC1Map tr root ∧
      c1Word tr frame root = TypedRecoveredWords.c1Value (fullC1Map tr root) := by
  have h := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x71 480 root frame j hread hpred
  have hm : rawC1Map tr frame root = fullC1Map tr root := by
    funext leaf
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun h (BinMultiproof.slots 18 leaf.val))
  exact ⟨hm, by unfold c1Word; rw [hm]⟩

theorem folded_word_stable
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (root : State) (frame : Bytes) (j : Fin 5) (hread : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    : rawFoldedMap tr frame root = fullFoldedMap tr root ∧
      foldedWord tr frame root = (fun q => FoldedRecoveredWord.wordOfPacked (fullFoldedMap tr root (MerkleIndexGeometry.foldedIndex q)) q) := by
  have h := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x72 128 root frame j hread hpred
  have hm : rawFoldedMap tr frame root = fullFoldedMap tr root := by
    funext leaf
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun h (BinMultiproof.slots 18 leaf.val))
  exact ⟨hm, by unfold foldedWord; rw [hm]⟩

theorem c1_opening_projects_word
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (root : State) (frame : Bytes) (j : Fin 5) (hread : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (i : Fin 1048576) (packed salt : Bytes) (hw : packed.length = 480)
    (hs : salt.length = 32)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (TypedRecoveredWords.queryLeaf i).val))
    (opened : TypedRecoveredWords.C1) (hdecode : MixedLeafDecoder.decodeC1 packed = some opened)
    (haccept : (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x71 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x71 packed salt))).1 a → Read tr a) :
    c1Word tr frame root i = opened (TypedRecoveredWords.querySlot i) := by
  have hd := BinThreeCommitmentTypedOpening.typed_opening_at_cut
    iv H tr Q hcons hQ hout 0x71 480 packed salt hw hs path root frame j
    hread hpred haccept hopen MixedLeafDecoder.decodeC1 opened hdecode
  change TypedRecoveredWords.decodeC1At (rawC1Map tr frame root)
    (TypedRecoveredWords.queryLeaf i) = some opened at hd
  simp only [c1Word, TypedRecoveredWords.c1Value, hd, Option.getD_some]

theorem folded_opening_projects_word
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (root : State) (frame : Bytes) (j : Fin 5) (hread : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (i : Fin 262144) (packed salt : Bytes) (hw : packed.length = 128)
    (hs : salt.length = 32)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (MerkleIndexGeometry.foldedIndex i).val))
    (opened : FoldedLeafCodec.Folded) (hdecode : FoldedLeafCodec.decodeFolded packed = some opened)
    (haccept : (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x72 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x72 packed salt))).1 a → Read tr a) :
    foldedWord tr frame root i = opened (FoldedRecoveredWord.foldedSlot i) := by
  have hd := BinThreeCommitmentTypedOpening.typed_opening_at_cut
    iv H tr Q hcons hQ hout 0x72 128 packed salt hw hs path root frame j
    hread hpred haccept hopen FoldedLeafCodec.decodeFolded opened hdecode
  change (rawFoldedMap tr frame root (MerkleIndexGeometry.foldedIndex i)).bind
    FoldedLeafCodec.decodeFolded = some opened at hd
  simp only [foldedWord, FoldedRecoveredWord.wordOfPacked, hd, Option.getD_some]

#print axioms c1_word_stable
#print axioms folded_word_stable
#print axioms c1_opening_projects_word
#print axioms folded_opening_projects_word
end AspisR1.BinSourceCommitmentWords
end
