import RPt_FIq_S_RawActualDecodeKMainStrictReadback

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainStrictReadback
open AspisR1DecodeKFullValueTrace (ParserTrace)

private theorem index_ok_iff (record : Slice U8) (i : Usize) (x : U8) :
    Slice.index_usize record i = ok x ↔ record.val[i.val]? = some x := by
  unfold Slice.index_usize
  cases h : record[i]? <;> simp_all

private theorem add_ok_val (a b c : Usize) (h : a + b = ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

private theorem read_after_add (record : Slice U8) (start delta index : Usize) (b : U8)
    (ha : start + delta = ok index)
    (hr : Slice.index_usize record index = ok b) :
    record.val[start.val + delta.val]? = some b := by
  have h := (index_ok_iff record index b).1 hr
  rw [add_ok_val start delta index ha] at h
  exact h

/-- Every byte of the actual assembled parser input occupies the exact
indexed position in the original record payload. Checked pointer arithmetic
and the individual reads supply this equality; it is not a caller premise. -/
theorem inputArray_payload_reads
    {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) (i : Fin 16) :
    (ParserTrace.payloadData trace).val[(ParserTrace.payloadStart trace).val + i.val]? =
      some ((inputArray trace).val[i.val]'(by simpa [(inputArray trace).property] using i.isLt)) := by
  fin_cases i <;> simp only [inputArray, Array.make, List.getElem_cons_zero, List.getElem_cons_succ]
  · simpa using (index_ok_iff _ _ _).1 (ParserTrace.hread0 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp1 trace) (ParserTrace.hread1 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp2 trace) (ParserTrace.hread2 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp3 trace) (ParserTrace.hread3 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp4 trace) (ParserTrace.hread4 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp5 trace) (ParserTrace.hread5 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp6 trace) (ParserTrace.hread6 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp7 trace) (ParserTrace.hread7 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp8 trace) (ParserTrace.hread8 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp9 trace) (ParserTrace.hread9 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp10 trace) (ParserTrace.hread10 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp11 trace) (ParserTrace.hread11 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp12 trace) (ParserTrace.hread12 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp13 trace) (ParserTrace.hread13 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp14 trace) (ParserTrace.hread14 trace)
  · exact read_after_add _ _ _ _ _ (ParserTrace.hp15 trace) (ParserTrace.hread15 trace)


/-- The assembled sixteen-byte array is the literal payload slice at the
actual checked start offset. -/
theorem inputArray_payload_slice
    {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) :
    (inputArray trace).val =
      ((ParserTrace.payloadData trace).val.drop (ParserTrace.payloadStart trace).val).take 16 := by
  have hlast := inputArray_payload_reads trace (15 : Fin 16)
  obtain ⟨hlastBound,_⟩ := List.getElem?_eq_some_iff.mp hlast
  have hfit : (ParserTrace.payloadStart trace).val + 16 ≤
      (ParserTrace.payloadData trace).val.length := by
    change (ParserTrace.payloadStart trace).val + 15 <
      (ParserTrace.payloadData trace).val.length at hlastBound
    omega
  have ha : (inputArray trace).val.length = 16 := (inputArray trace).property
  apply List.ext_getElem
  · simp only [ha,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have hi16 : i < 16 := by omega
    have hread := inputArray_payload_reads trace ⟨i,hi16⟩
    obtain ⟨_,hvalue⟩ := List.getElem?_eq_some_iff.mp hread
    simpa only [List.getElem_take,List.getElem_drop] using hvalue.symm

/-- The actual payload accessor strips exactly the five framing bytes. -/
theorem payloadData_eq_drop
    {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) :
    (ParserTrace.payloadData trace).val = r.framed.val.drop 5 := by
  have h := ParserTrace.hpayload trace
  simp only [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload,
    core.slice.index.Slice.index,core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index] at h
  split at h
  · have he := Result.ok.inj h
    rw [← he]
    rfl
  · cases h

/-- The offset is the checked starting byte offset plus the literal 32-byte
stride times the selected coefficient index. -/
theorem payloadStart_eq
    {r : DecodeRecord} {byteOffset value offset : Usize} {q : DecodeQM}
    (trace : Trace r byteOffset value offset q) :
    (ParserTrace.payloadStart trace).val = byteOffset.val + value.val * 32 := by
  have hs := add_ok_val _ _ _ (ParserTrace.hstart trace)
  have hm := UScalar.mul_equiv value (32#usize)
  have hmul := ParserTrace.hoffsetMul trace
  change UScalar.mul value (32#usize) = .ok (ParserTrace.strideValue trace) at hmul
  rw [hmul] at hm
  rw [hs,hm.2.1]
  rfl

#print axioms inputArray_payload_slice
#print axioms payloadData_eq_drop
#print axioms payloadStart_eq

#print axioms inputArray_payload_reads
end AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
