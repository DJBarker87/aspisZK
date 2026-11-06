import JFw_Chunks
import ExtractedPrefixParserAgreement
set_option autoImplicit false
namespace AspisR1.JFw_Record
open Aeneas Aeneas.Std Result
open AspisR1RecordParser

theorem index (frame : Slice U8) (tag a b c d : U8) (payload : Slice U8)
    (bytes : frame.val = tag::a::b::c::d::payload.val) :
    Slice.index_usize frame 0#usize = ok tag ∧
    Slice.index_usize frame 1#usize = ok a ∧
    Slice.index_usize frame 2#usize = ok b ∧
    Slice.index_usize frame 3#usize = ok c ∧
    Slice.index_usize frame 4#usize = ok d := by
  simp [Slice.index_usize,bytes]

theorem success (row tag a b c d : U8) (size : Usize) (frame payload : Slice U8)
    (shape : r1_wire.row_shape row = ok (some (tag,size)))
    (small : size.val ≤ 3712) (length : payload.length = size.val)
    (bytes : frame.val = tag::a::b::c::d::payload.val)
    (header : UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) = size)
    (fields : 14 ≤ row.val → r1_wire.validate_record_fields row payload = ok (.Ok ())) :
    r1_wire.parse_record row frame = ok (.Ok payload) := by
  obtain ⟨total,add,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
  have flen : Slice.len frame = total := by
    apply UScalar.eq_of_val_eq
    change frame.length = total.val
    simp only [Slice.length,bytes,List.length_cons] at *
    scalar_tac
  obtain ⟨r0,r1,r2,r3,r4⟩ := index frame tag a b c d payload bytes
  have readPayload : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8) frame {start:=5#usize} = ok payload := by
    simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst]
    unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index
    have enough : (5#usize).val ≤ frame.length := by
      change 5 ≤ frame.val.length
      rw [bytes]
      simp only [List.length_cons]
      omega
    simp only [if_pos enough]
    apply congrArg Result.ok
    apply Subtype.ext
    simp [bytes,List.slice]
  have finish : (do
      let i1 ← 5#usize + size
      if total != i1 then ok (.Err (r1_wire.Error.Length row))
      else if tag != tag then ok (.Err (r1_wire.Error.Tag row))
      else if size != size then ok (.Err (r1_wire.Error.Length row))
      else ok (.Ok payload) : Result (core.result.Result (Slice U8) r1_wire.Error)) = ok (.Ok payload) := by
    rw [add]
    simp only [bind_tc_ok,bne_self_eq_false,Bool.false_eq_true,if_false]
  unfold r1_wire.parse_record
  rw [shape]
  simp (config := {zeta := true}) only [AspisR1RecordParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  simp (config := {zeta := true}) only [add,bind_tc_ok,flen,bne_self_eq_false,
    Bool.false_eq_true,if_false,r0,r1,r2,r3,r4,lift,header,readPayload]
  by_cases active : 14 ≤ row.val
  · have test : row ≥ 14#u8 := by scalar_tac
    simp only [test,decide_true,if_true,fields active,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact finish
  · have test : ¬ row ≥ 14#u8 := by scalar_tac
    simp only [test,decide_false,if_false]

    exact finish

#print axioms index
#print axioms success
end AspisR1.JFw_Record
