import BinSourceCommitmentLiteral

/-! Strict binary opening projections at the actual source commitment frames.
Acceptance, strict decoding and read containment remain explicit R13/R10 gates. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.BinSourceCommitmentOpening
open Aeneas Aeneas.Std Result AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open BinSourceCommitmentWords BinSourceCommitmentFrames SourceGlobalOracleInitial
open SourceDigestAddresses

theorem actual_initial_opening_projects_word
    {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pub root before)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (hlog : initPair init ∈ tr)
    (i : Fin 1048576) (packed salt : Bytes) (hw : packed.length = 480)
    (hs : salt.length = 32)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (TypedRecoveredWords.queryLeaf i).val))
    (opened : TypedRecoveredWords.C1) (hdecode : MixedLeafDecoder.decodeC1 packed = some opened)
    (haccept : (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x71 packed salt))).2 = decodeState root)
    (hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x71 packed salt))).1 a → Read tr a) :
    c1Word tr (initPair init).1 (decodeState root) i = opened (TypedRecoveredWords.querySlot i) := by
  obtain ⟨hr,hp⟩ := initial_read_target init tr hlog
  exact c1_opening_projects_word iv H tr Q hcons hQ hout (decodeState root) _
    2 hr hp i packed salt hw hs path opened hdecode haccept hopen

theorem actual_folded_opening_projects_word
    (state root absorbed : TranscriptStep.Bytes32) (payload : Slice U8) (tail : Bytes)
    (hpayload : rawBytes payload = bytes (decodeState root) ++ tail)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (hlog : (flatten (CallerStep.openingAbsorbParts state 190#u8 256#u32 payload),
      decodeState absorbed) ∈ tr)
    (i : Fin 262144) (packed salt : Bytes) (hw : packed.length = 128)
    (hs : salt.length = 32)
    (path : BinMerkle32Path.Path (BinMultiproof.slots 18 (MerkleIndexGeometry.foldedIndex i).val))
    (opened : FoldedLeafCodec.Folded) (hdecode : FoldedLeafCodec.decodeFolded packed = some opened)
    (haccept : (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x72 packed salt))).2 = decodeState root)
    (hopen : ∀ a, Read (eval H (BinMerkleProgram.leafProgram path
      (BinMerkle32Leaf.leafInput 0x72 packed salt))).1 a → Read tr a) :
    foldedWord tr (CommitmentRootFrames.foldedFrame (decodeState state) (decodeState root) tail) (decodeState root) i = opened (FoldedRecoveredWord.foldedSlot i) := by
  obtain ⟨hr,hp⟩ := folded_read_target state root absorbed payload tail hpayload tr hlog
  exact folded_opening_projects_word iv H tr Q hcons hQ hout (decodeState root) _
    3 hr hp i packed salt hw hs path opened hdecode haccept hopen

#print axioms actual_initial_opening_projects_word
#print axioms actual_folded_opening_projects_word
end AspisR1PublicPreparation.BinSourceCommitmentOpening
end
