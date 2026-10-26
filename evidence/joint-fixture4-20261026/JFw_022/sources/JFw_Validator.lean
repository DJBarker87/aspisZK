import ExtractedRecordValidator
set_option autoImplicit false
namespace AspisR1.JFw_Validator
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1RecordParser ExtractedRecordValidator ExtractedRecordHighZero

theorem loop_valid (chunks : List (Slice U8)) (remainder : Slice U8) (count : Usize) (row : U8)
    (bounded : count.val+chunks.length ≤ Usize.max)
    (valid : ∀ chunk ∈ chunks,ChunkValid chunk) :
    r1_wire.validate_record_fields_loop ⟨⟨chunks,remainder⟩,count⟩ row = ok (.Ok ()) := by
  induction chunks generalizing count with
  | nil =>
    rw [loop_unroll]
    simp [r1_wire.validate_record_fields_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorChunksExact.next]
  | cons chunk chunks ih =>
    have addBound : count.val+1 ≤ Usize.max := by simp only [List.length_cons] at bounded;omega
    obtain ⟨count',add,value⟩ := UScalar.add_spec (x:=count) (y:=1#usize) addBound
    let next : Iter := ⟨⟨chunks,remainder⟩,count'⟩
    have advance : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorChunksExact U8) (⟨⟨chunk::chunks,remainder⟩,count⟩ : Iter) =
        ok (some (count,chunk),next) := by
      simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next,bind_tc_ok,add]
      rfl
    obtain ⟨w,decode,zero⟩ := valid chunk (List.mem_cons_self ..)
    have guard := (qm31_ne_false_iff w.c1 field.QM31.ZERO).mpr zero
    have body : r1_wire.validate_record_fields_loop.body row (⟨⟨chunk::chunks,remainder⟩,count⟩ : Iter) =
        ok (.cont next) := by
      unfold r1_wire.validate_record_fields_loop.body
      rw [advance]
      change (do
        let result ← field.wide_exact.WideExact.from_le_bytes chunk
        _) = _
      rw [decode]
      simp only [bind_tc_ok,AspisR1RecordParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,field.wide_exact.WideExact.impl.c1]
      rw [guard]
      rfl
    rw [loop_unroll,body]
    change r1_wire.validate_record_fields_loop next row = ok (.Ok ())
    exact ih count' (by simp only [List.length_cons] at bounded;change count'.val=count.val+1 at value;omega)
      (fun c hc => valid c (List.mem_cons_of_mem _ hc))

#print axioms loop_valid
end AspisR1.JFw_Validator
