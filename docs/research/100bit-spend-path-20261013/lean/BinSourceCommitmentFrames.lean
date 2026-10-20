import RawSourceGlobalOracleInitial
import RawSamplerSuffixSourceBridge
import BinRawByteCollisionTargets
import R1CommitmentRootFrames

/-! Actual source input frames for C1 and the second commitment.
The folded payload equality is a named codec/caller obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.BinSourceCommitmentFrames
open Aeneas Aeneas.Std Result AspisR1
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open SourceDigestAddresses SourceGlobalOracleInitial

theorem initial_frame {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (c : PublicInitCall D pub root before) :
    (initPair c).1 = PublicInitFrame.frame
      (rawBytes (alloc.vec.Vec.deref c.encoded)) (decodeState root) := by
  change flatten (TranscriptStep.initParts _ root c.length) = _
  rw [flatten_init, successful_length _ _ c.converted]
  rfl

theorem initial_target {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (c : PublicInitCall D pub root before) :
    BinRawByteCollisionTargets.pred 2 (initPair c).1 = some (decodeState root) := by
  rw [initial_frame, BinRawByteCollisionTargets.pred_tail]
  exact BinRawByteCollisionTargets.trailing_frame _ _

theorem initial_read_target {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (c : PublicInitCall D pub root before) (tr : List (Bytes × State))
    (hlog : initPair c ∈ tr) :
    Read tr (initPair c).1 ∧
      BinRawByteCollisionTargets.pred 2 (initPair c).1 = some (decodeState root) := by
  exact ⟨List.mem_map.mpr ⟨initPair c,hlog,rfl⟩,initial_target c⟩

/-- The actual row-30 opening absorb preimage. The explicit 256-byte source
length and digest||polynomial payload are the remaining caller/codec join. -/
theorem folded_frame (state root : TranscriptStep.Bytes32) (payload : Slice U8)
    (tail : Bytes) (hpayload : rawBytes payload = bytes (decodeState root) ++ tail) :
    flatten (CallerStep.openingAbsorbParts state 190#u8 256#u32 payload) =
      CommitmentRootFrames.foldedFrame (decodeState state) (decodeState root) tail := by
  rw [SamplerSuffixSourceFrames.opening_absorb_frame, hpayload]
  simp only [CommitmentRootFrames.foldedFrame, CommitmentRootFrames.foldedPrefix,
    PublicInitFrame.lengthBytes, List.ofFn_succ, List.ofFn_zero,
    List.append_assoc]
  rfl

theorem folded_target (state root : TranscriptStep.Bytes32) (payload : Slice U8)
    (tail : Bytes) (hpayload : rawBytes payload = bytes (decodeState root) ++ tail) :
    BinRawByteCollisionTargets.pred 3
      (flatten (CallerStep.openingAbsorbParts state 190#u8 256#u32 payload)) =
      some (decodeState root) := by
  rw [folded_frame state root payload tail hpayload, BinRawByteCollisionTargets.pred_middle]
  exact BinRawByteCollisionTargets.fixed_frame 38 _ _ _
    (CommitmentRootFrames.foldedPrefix_length _)

theorem folded_read_target (state root absorbed : TranscriptStep.Bytes32)
    (payload : Slice U8) (tail : Bytes)
    (hpayload : rawBytes payload = bytes (decodeState root) ++ tail)
    (tr : List (Bytes × State))
    (hlog : (flatten (CallerStep.openingAbsorbParts state 190#u8 256#u32 payload),
      decodeState absorbed) ∈ tr) :
    Read tr (CommitmentRootFrames.foldedFrame (decodeState state) (decodeState root) tail) ∧
    BinRawByteCollisionTargets.pred 3
      (CommitmentRootFrames.foldedFrame (decodeState state) (decodeState root) tail) =
      some (decodeState root) := by
  have hf := folded_frame state root payload tail hpayload
  exact ⟨List.mem_map.mpr ⟨_,hlog,hf⟩, hf ▸ folded_target state root payload tail hpayload⟩

#print axioms initial_frame
#print axioms initial_target
#print axioms initial_read_target
#print axioms folded_frame
#print axioms folded_target
#print axioms folded_read_target
end AspisR1PublicPreparation.BinSourceCommitmentFrames
end
