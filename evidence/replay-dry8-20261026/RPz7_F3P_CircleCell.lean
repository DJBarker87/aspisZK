import RPz7_F3P_YCells
import RPz7_PAln_CircleDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_CircleCell
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem decoded (row : Fin 2) (frame : Bytes) (values : CircleRecordCodec.Payload row)
    (h : CircleRecordCodec.decode row frame=some values) (j : Fin (CircleRecordCodec.count row)) :
    SemanticCoefficientCodec.decodeLow (((frame.drop 5).drop (32*j.val)).take 32)=some (values j) := by
  obtain ⟨raw,parsed,read⟩ := Option.bind_eq_some_iff.mp h
  have payload := (RecordFrameCodec.parse_sound _ _ _ raw parsed).2
  have length := (RecordFrameCodec.parse_sound _ _ _ raw parsed).1
  have bytes : frame.drop 5=raw := by
    rw [payload]
    simp only [RecordFrameCodec.frame,RecordFrameCodec.header,List.length_cons,List.length_map,List.length_range]
    simp [PublicInitFrame.lengthBytes]
  rw [bytes]
  exact (SelectedFieldSequenceCodec.decodeLow_eq_some_iff raw values).mp read |>.2 j

#print axioms decoded
end AspisR1.F3P_CircleCell
end
