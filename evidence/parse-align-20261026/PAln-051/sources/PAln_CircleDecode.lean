import PAln_SemanticLayout
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_CircleDecode
open AspisV8R19.DuplexFrames OraclePortCompactDraft PAln_SemanticLayout

theorem decode_first (frame : Bytes) (layout : Frame 25 frame) :
    ∃ value, CircleRecordCodec.decode 0 frame=some value := by
  obtain ⟨payload,length,canonical,same⟩ := layout
  have length' : payload.length=16*116 := length
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.low_encode_exists 116 payload length' (canonical (by decide))
  refine ⟨values,?_⟩
  have frameEq : frame=CircleRecordCodec.encode (row := 0) values := by
    rw [same]
    change (4::le32 3712)++expand 116 payload=
      (4::le32 3712)++SelectedFieldSequenceCodec.encodeLow values
    exact congrArg (fun bs => (4::le32 3712)++bs) encoded.symm
  rw [frameEq]
  exact CircleRecordCodec.decode_encode (row := 0) values

theorem decode_second (frame : Bytes) (layout : Frame 26 frame) :
    ∃ value, CircleRecordCodec.decode 1 frame=some value := by
  obtain ⟨payload,length,canonical,same⟩ := layout
  have length' : payload.length=16*29 := length
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.low_encode_exists 29 payload length' (canonical (by decide))
  refine ⟨values,?_⟩
  have frameEq : frame=CircleRecordCodec.encode (row := 1) values := by
    rw [same]
    change (5::le32 928)++expand 29 payload=
      (5::le32 928)++SelectedFieldSequenceCodec.encodeLow values
    exact congrArg (fun bs => (5::le32 928)++bs) encoded.symm
  rw [frameEq]
  exact CircleRecordCodec.decode_encode (row := 1) values

theorem row25 (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic) :
    ∃ value, CircleRecordCodec.decode 0 (rowBytes p 25)=some value := by
  have length := PSem_Rows.semanticRows_length _ _ _ _ rows
  let frame := p.semantic[25]'(by omega)
  have slot : p.semantic[25]?=some frame := List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
  have shape := at_index 0 p.semantic (layout _ _ _ _ rows) 25 frame slot
  have row : rowBytes p 25=frame := by simp [rowBytes,slot]
  rw [row]
  exact decode_first frame shape

theorem row26 (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic) :
    ∃ value, CircleRecordCodec.decode 1 (rowBytes p 26)=some value := by
  have length := PSem_Rows.semanticRows_length _ _ _ _ rows
  let frame := p.semantic[26]'(by omega)
  have slot : p.semantic[26]?=some frame := List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
  have shape := at_index 0 p.semantic (layout _ _ _ _ rows) 26 frame slot
  have row : rowBytes p 26=frame := by simp [rowBytes,slot]
  rw [row]
  exact decode_second frame shape

#print axioms decode_first
#print axioms decode_second
#print axioms row25
#print axioms row26
end AspisR1.PAln_CircleDecode
end
