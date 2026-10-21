import OraclePortCandidateWordsC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRootBytesC6
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortBatchDraft

theorem framed_drop (b : Bytes) : (framed b).drop 4 = b := by
  unfold framed
  have length : (le32 b.length).length = 4 := by simp only [le32,List.length_map,List.length_range]
  rw [← length,List.drop_left]

theorem lengthFrame_drop (b : Bytes) : (LengthFrameCodec.frame b).drop 4 = b := by
  unfold LengthFrameCodec.frame
  rw [← PublicInitFrame.lengthBytes_length b.length,List.drop_left]

theorem c2_drop (root : State) :
    (SemanticRecordCodec.encode (⟨.c2Root root,rfl⟩ : SemanticRecordCodec.RowPayload 2)).drop 5 = bytes root := by
  change (RecordFrameCodec.frame 1 (bytes root)).drop 5 = bytes root
  unfold RecordFrameCodec.frame
  rw [← RecordFrameCodec.header_length (1 : Byte) (bytes root).length,List.drop_left]

theorem initial (p : Parsed) (root : State) (same : root0 p = bytes root) : committedRoot p 0 = root := by
  simp only [committedRoot,ite_true,same,SemanticRecordCodec.decodeState_bytes,Option.getD_some]

theorem second (p : Parsed) (root : State)
    (same : p.semantic[2]?.getD [] =
      SemanticRecordCodec.encode (⟨.c2Root root,rfl⟩ : SemanticRecordCodec.RowPayload 2)) :
    committedRoot p 1 = root := by
  simp only [committedRoot,show (1:Nat) ≠ 0 by decide,ite_false,ite_true,same,c2_drop,
    SemanticRecordCodec.decodeState_bytes,Option.getD_some]

theorem row30_root (p : Parsed) : ((rowBytes p 30).drop 4).take 32 = root2 p := by
  simp only [rowBytes,show ¬ (30:Nat) < 27 by decide,show (30:Nat) ≠ 27 by decide,
    show (30:Nat) ≠ 28 by decide,show (30:Nat) ≠ 29 by decide,ite_false,ite_true,framed_drop]
  simp only [slice,List.take_take,root2]

theorem folded (p : Parsed) (payload : OpeningRecordCodec.Payload .second)
    (same : rowBytes p 30 = OpeningRecordCodec.encode payload) : committedRoot p 2 = payload.1 := by
  have roots := congrArg (fun b : Bytes => (b.drop 4).take 32) same
  rw [row30_root] at roots
  change root2 p = ((LengthFrameCodec.frame
    (bytes payload.1 ++ SelectedFieldSequenceCodec.encodeWide payload.2)).drop 4).take 32 at roots
  rw [lengthFrame_drop] at roots
  have take : (bytes payload.1 ++ SelectedFieldSequenceCodec.encodeWide payload.2).take 32 = bytes payload.1 := by
    simpa only [bytes_length] using List.take_left (bytes payload.1) (SelectedFieldSequenceCodec.encodeWide payload.2)
  rw [take] at roots
  simp only [committedRoot,show (2:Nat) ≠ 0 by decide,show (2:Nat) ≠ 1 by decide,ite_false,
    roots,SemanticRecordCodec.decodeState_bytes,Option.getD_some]

#print axioms framed_drop
#print axioms lengthFrame_drop
#print axioms c2_drop
#print axioms initial
#print axioms second
#print axioms row30_root
#print axioms folded
end AspisR1.OraclePortRootBytesC6
end
