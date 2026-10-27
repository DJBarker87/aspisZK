import JFw_Record
set_option autoImplicit false
namespace AspisR1.JFw_RecordAt
open Aeneas Aeneas.Std Result
open AspisR1PrefixAggregateParser

theorem success (bytes frame payload : Slice U8) (row tag : U8) (size offset next : Usize)
    (shape : AspisR1RecordParser.r1_wire.row_shape row = ok (some (tag,size)))
    (nextValue : next.val = offset.val+5+size.val)
    (bound : next.val ≤ bytes.length)
    (raw : (bytes.val.drop offset.val).take (5+size.val) = frame.val)
    (accepted : r1_wire.parse_record row frame = ok (.Ok payload)) :
    r1_wire.parse_record_at bytes row offset = ok (.Ok (frame,next)) := by
  obtain ⟨length,add,lengthValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
  have addNext : offset+length = ok next := by
    obtain ⟨actual,call,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=offset) (y:=length) (by scalar_tac))
    have eq : actual = next := UScalar.eq_of_val_eq (by scalar_tac)
    simpa only [eq] using call
  have get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=next} = ok (some frame) := by
    simp only [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice]
    unfold core.slice.index.SliceIndexRangeUsizeSlice.get
    have bounds : offset ≤ next ∧ next ≤ bytes.length := by scalar_tac
    rw [if_pos bounds]
    apply congrArg Result.ok
    apply congrArg Option.some
    apply Subtype.ext
    change List.slice offset.val next.val bytes.val = frame.val
    simp only [List.slice]
    have width : next.val-offset.val = 5+size.val := by omega
    rw [width]
    exact raw
  have currentShape : r1_wire.row_shape row = ok (some (tag,size)) := by
    rw [ExtractedPrefixRecordAgreement.row_shape_agreement]
    exact shape
  unfold r1_wire.parse_record_at
  rw [currentShape]
  simp (config := {zeta := true}) only [bind_tc_ok,core.option.Option.unwrap]
  change (do
    let length ← 5#usize + size
    let endPos ← offset + length
    let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=endPos}
    let r ← AspisR1PrefixAggregateParser.core.option.Option.ok_or o (r1_wire.Error.Length row)
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue frame => do
      let status ← r1_wire.parse_record row frame
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch status
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (.Ok (frame,endPos))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Slice U8 × Usize) (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Slice U8 × Usize) (core.convert.FromSame r1_wire.Error) residual) = _
  rw [add]
  simp only [bind_tc_ok,addNext,get,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,accepted]

#print axioms success
end AspisR1.JFw_RecordAt
