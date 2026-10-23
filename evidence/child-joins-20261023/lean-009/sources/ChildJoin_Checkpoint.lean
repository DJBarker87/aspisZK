import ChildJoin_Decoder
import CheckpointBytes5Join

/-! Fixed-header results for the concrete cone endpoints. These do not install
opaque adapter op10/op11 as these endpoints. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ChildJoin_Checkpoint
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft CheckpointBytes5Effect
open CheckpointBytes5Inputs CheckpointBytesDigest ChildJoin_Decoder

theorem writer_header {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : Oracle D hash H)
    (wp : CheckpointBytes5Writer.Prepared) (wa : CheckpointBytes5Writer.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (provenance : CheckpointBytes5Join.S1S7S8StateProvenance wp wa pm am)
    (proof public1 ck : Slice U8) (before after : Log)
    (success : run D hash (CheckpointBytes5Writer.writer wp wa proof public1) before = ok (ck,after)) :
    checkpointHeader (bytesOf ck.val) = some (H (bytesOf proof.val),H (bytesOf public1.val)) ∧
      ck.val.length = 1768 := by
  obtain ⟨encoding,_⟩ := CheckpointBytes5Writer.writer_effects D hash H oracle wp wa proof public1 ck
    provenance.size provenance.queriesBound provenance.canonical provenance.next before after success
  dsimp only at encoding
  constructor
  · rw [encoding]
    exact encoded_header H _ _ _ _
  · have length := congrArg List.length encoding
    simpa only [bytesOf,List.length_map,OraclePortCheckpointAbiC5.encode_length] using length

theorem checked_wire (ck actual : Slice U8) (start finish : Usize)
    (success : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      ck {start := start, «end» := finish} = ok actual) :
    bytesOf actual.val = slice (bytesOf ck.val) start.val (finish.val-start.val) := by
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at success
  split at success
  · have same := congrArg Subtype.val (Result.ok.inj success)
    rw [← same]
    simp only [bytesOf,slice,List.slice,List.map_take,List.map_drop]
  · cases success

theorem reader_header (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : Oracle D hash H)
    (ck proof public1 : Slice U8)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (success : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      D ck proof public1 .S2 hash = ok (.Ok (p,a))) :
    checkpointHeader (bytesOf ck.val) = some (H (bytesOf proof.val),H (bytesOf public1.val)) := by
  obtain ⟨calls⟩ := CheckpointBytes4Comparison.successful_calls reserved D ck proof public1 .S2 hash p a success
  have hp := checked_wire ck calls.storedProof 16#usize 48#usize calls.proofField
  have hu := checked_wire ck calls.storedPublic 48#usize 80#usize calls.publicField
  have pp : calls.proofParts = AspisR1Stage2.WireTx2.singletonParts proof := by
    simpa only [lift,AspisR1Stage2.WireTx2.singletonParts,Result.ok.injEq] using calls.proofInput.symm
  have pu : calls.publicParts = AspisR1Stage2.WireTx2.singletonParts public1 := by
    simpa only [lift,AspisR1Stage2.WireTx2.singletonParts,Result.ok.injEq] using calls.publicInput.symm
  have proofHash := oracle _ _ calls.proofCall
  have publicHash := oracle _ _ calls.publicCall
  rw [pp,singleton_input] at proofHash
  rw [pu,singleton_input] at publicHash
  have proofBytes : slice (bytesOf ck.val) 16 32 = bytes (H (bytesOf proof.val)) := by
    rw [← proofHash,bytes_stateOf,← calls.proofEqual]
    exact hp.symm
  have publicBytes : slice (bytesOf ck.val) 48 32 = bytes (H (bytesOf public1.val)) := by
    rw [← publicHash,bytes_stateOf,← calls.publicEqual]
    exact hu.symm
  simp only [checkpointHeader,proofBytes,publicBytes,digest_bytes,Option.bind_eq_bind,Option.bind_some,pure]

#print axioms writer_header
#print axioms checked_wire
#print axioms reader_header
end AspisR1.ChildJoin_Checkpoint
end
