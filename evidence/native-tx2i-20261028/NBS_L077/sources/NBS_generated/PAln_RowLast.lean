import PAln_OpeningDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_RowLast
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open PAln_RowBounds PAln_SubSlice PAln_OpeningDecode

theorem state_exists (b : Bytes) (length : b.length=32) : ∃ root : State, bytes root=b := by
  let root : State := fun i => b[i.val]'(by omega)
  refine ⟨root,?_⟩
  apply List.ext_getElem
  · simp [bytes,length]
  · intro i hi hj
    simp only [bytes,List.getElem_ofFn,root]

theorem second (p : Parsed) (length : p.wire.length=57607) (scan : scan p.wire) :
    ∃ value, OpeningRecordCodec.decode .second (rowBytes p 30)=some value := by
  have region : (slice p.wire 7783 2272).length=2272 := slice_length _ _ _ (by omega)
  have checked := canonical_slice (slice p.wire 7783 2272) 0 224 scan.2.2.1
    (by decide) (by decide) (by omega)
  rw [nested _ _ _ _ _ (by decide)] at checked
  have len : (slice p.wire 7783 224).length=32*7 := slice_length _ _ _ (by omega)
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.wide_encode_exists 7 _ len checked
  obtain ⟨root,rootBytes⟩ := state_exists (slice p.wire 7751 32) (slice_length _ _ _ (by omega))
  have split : slice p.wire 7751 256=slice p.wire 7751 32++slice p.wire 7783 224 := by
    change (p.wire.drop 7751).take (32+224)=_
    rw [List.take_add]
    simp only [slice,List.drop_drop]
  refine ⟨(root,values),?_⟩
  have row : rowBytes p 30=framed (slice p.wire 7751 256) := by simp [rowBytes]
  rw [row,framed_eq,split,←rootBytes,←encoded]
  exact OpeningRecordCodec.decode_encode (row := .second) (root,values)

theorem final (p : Parsed) (length : p.wire.length=57607) (scan : scan p.wire) :
    ∃ value, OpeningRecordCodec.decode .final (rowBytes p 31)=some value := by
  have region : (slice p.wire 7783 2272).length=2272 := slice_length _ _ _ (by omega)
  have checked := canonical_slice (slice p.wire 7783 2272) 224 2048 scan.2.2.1
    (by decide) (by decide) (by omega)
  rw [nested _ _ _ _ _ (by decide)] at checked
  have len : (slice p.wire 8007 2048).length=32*64 := slice_length _ _ _ (by omega)
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.wide_encode_exists 64 _ len checked
  refine ⟨values,?_⟩
  have row : rowBytes p 31=framed (slice p.wire 8007 2048) := by simp [rowBytes]
  rw [row,framed_eq,←encoded]
  exact OpeningRecordCodec.decode_encode (row := .final) values

#print axioms state_exists
#print axioms second
#print axioms final
end AspisR1.PAln_RowLast
end
