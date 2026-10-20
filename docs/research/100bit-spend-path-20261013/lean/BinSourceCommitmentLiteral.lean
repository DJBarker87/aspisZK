import BinSourceCommitmentFrames
import BinSourceCommitmentWords

/-! Install the binary causal words in the actual row-0/30 constructors.
Caller reachability, global log composition and arithmetic transport remain
explicit, as in the suffix sampler packet. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.BinSourceCommitmentLiteral
open Aeneas Aeneas.Std Result AspisR1 AspisR1.TranscriptView
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open SourceDigestAddresses SourceGlobalOracleInitial BinSourceCommitmentFrames
open BinSourceCommitmentWords BinCanonicalCutWords

theorem actual_initial_word_stable {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pub root before)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hlog : initPair init ∈ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr) :
    c1Word tr (initPair init).1 (decodeState root) =
      TypedRecoveredWords.c1Value (fullC1Map tr (decodeState root)) := by
  obtain ⟨hr,hp⟩ := initial_read_target init tr hlog
  exact (c1_word_stable iv H tr Q hcons hQ hout (decodeState root) _ 2 hr hp).2

theorem actual_row0_with_causal_word
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (root : TranscriptStep.Bytes32)
    (c : SourceFull25.Call D pre) (init : PublicInitCall D pub root c.before)
    (hrow : c.row.val = 0)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hinitLog : initPair init ∈ tr) (hsource : SourceDigestLog.sourceLog [c] ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (hbound : (rawBytes c.record.framed).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hpublic : P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref init.encoded))
    (hempty : rawBytes c.record.framed = PublicInitFrame.emptyRecord) :
    let word := c1Word tr (initPair init).1 (decodeState root)
    LiteralTranscript.valid 0 (.initial (decodeState root) word) ∧
    Value.ordinary (SourceLiteralTraceLift.sourceChallenge c) =
      (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
        (LiteralTranscript.samp 0 P (.initial (decodeState root) word)).toProgram).2.1 ∧
    decodeState c.after.state =
      (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
        (LiteralTranscript.samp 0 P (.initial (decodeState root) word)).toProgram).2.2 ∧
    word = TypedRecoveredWords.c1Value (fullC1Map tr (decodeState root)) := by
  have hs := initializer_state_from_log init H tr hinitLog hcons P (decodeState root) hpublic rfl
  have hb : ∀ d ∈ [c], (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact hbound
  have hc := SourceGlobalOracleInitial.call_simulates_literal_initial [c] c (by simp)
    H tr hsource hcons hb hrow P (decodeState root)
    (c1Word tr (initPair init).1 (decodeState root)) hs hempty
  exact ⟨by trivial,hc.1,hc.2,
    actual_initial_word_stable init iv H tr Q hinitLog hcons hQ hout⟩

theorem actual_folded_word_stable
    (state root absorbed : TranscriptStep.Bytes32) (payload : Slice U8) (tail : Bytes)
    (hpayload : rawBytes payload = bytes (decodeState root) ++ tail)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hlog : (flatten (CallerStep.openingAbsorbParts state 190#u8 256#u32 payload),
      decodeState absorbed) ∈ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr) :
    foldedWord tr (CommitmentRootFrames.foldedFrame (decodeState state) (decodeState root) tail)
      (decodeState root) =
      (fun q => FoldedRecoveredWord.wordOfPacked (fullFoldedMap tr (decodeState root)
        (MerkleIndexGeometry.foldedIndex q)) q) := by
  obtain ⟨hr,hp⟩ := folded_read_target state root absorbed payload tail hpayload tr hlog
  exact (folded_word_stable iv H tr Q hcons hQ hout (decodeState root) _ 3 hr hp).2

theorem actual_row30_with_causal_word {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : transcript.Transcript Hash) (root absorbed block : TranscriptStep.Bytes32)
    (payload : Slice U8) (tail : Bytes)
    (hpayload : rawBytes payload = bytes (decodeState root) ++ tail)
    (hcall : transcript.Transcript.block D self 30#u8 payload = ok (block,after))
    (hlen : UScalar.cast .U32 (Slice.len payload) = 256#u32)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hlog : (flatten (CallerStep.openingAbsorbParts self.state 190#u8 256#u32 payload),
      decodeState absorbed) ∈ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts))
    (P : LiteralTranscript.Prefix) (b : SelectedTranscriptParams.Message)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b =
      PublicInitFrame.lengthBytes 256 ++ rawBytes payload) :
    let word := foldedWord tr
      (CommitmentRootFrames.foldedFrame (decodeState self.state) (decodeState root) tail)
      (decodeState root)
    LiteralTranscript.valid 30 (.second b word) ∧
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 30 P (.second b word)).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 30 (decodeState block)),decodeState after.state) ∧
    word = (fun q => FoldedRecoveredWord.wordOfPacked (fullFoldedMap tr (decodeState root)
      (MerkleIndexGeometry.foldedIndex q)) q) := by
  refine ⟨by trivial, ?_, actual_folded_word_stable self.state root absorbed payload tail
    hpayload iv H tr Q hlog hcons hQ hout⟩
  exact SamplerSuffixSourceBridge.opening_block_correspondence D self after 30#u8 190#u8
    payload 256#u32 block hcall (by rfl) hlen P 30 (by omega) rfl _ b rfl
    hstate hbytes H hdigest

#print axioms actual_initial_word_stable
#print axioms actual_row0_with_causal_word
#print axioms actual_folded_word_stable
#print axioms actual_row30_with_causal_word
end AspisR1PublicPreparation.BinSourceCommitmentLiteral
end
