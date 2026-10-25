import ExtractedPrefixLoopMap

/-! Actual generated record-parser agreement under explicit carrier maps. -/
namespace AspisR1.ExtractedPrefixRecordAgreement
open Aeneas Aeneas.Std Result ControlFlow
open ExtractedPrefixFieldAgreement ExtractedPrefixLoopMap

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8)

def errorToRecord : AspisR1PrefixAggregateParser.r1_wire.Error →
    AspisR1RecordParser.r1_wire.Error
  | .Allocation => .Allocation
  | .RowOrder expected actual => .RowOrder expected actual
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row index => .NonCanonical row index
  | .Boundary index => .Boundary index
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

def statusToRecord {α : Type} :
    core.result.Result α AspisR1PrefixAggregateParser.r1_wire.Error →
    core.result.Result α AspisR1RecordParser.r1_wire.Error
  | .Ok value => .Ok value
  | .Err error => .Err (errorToRecord error)

theorem row_shape_agreement (row : U8) :
    AspisR1PrefixAggregateParser.r1_wire.row_shape row =
      AspisR1RecordParser.r1_wire.row_shape row := by
  unfold AspisR1PrefixAggregateParser.r1_wire.row_shape
    AspisR1RecordParser.r1_wire.row_shape
    AspisR1PrefixAggregateParser.r1_wire.CLAIMS AspisR1RecordParser.r1_wire.CLAIMS
    AspisR1PrefixAggregateParser.r1_wire.LANES AspisR1RecordParser.r1_wire.LANES
    AspisR1PrefixAggregateParser.r1_wire.POINTS AspisR1RecordParser.r1_wire.POINTS
  rfl

theorem body_agreement (row : U8) (iter : Iter) :
    mapResult (mapControl statusToRecord)
      (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body row iter) =
      AspisR1RecordParser.r1_wire.validate_record_fields_loop.body row iter := by
  unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body
    AspisR1RecordParser.r1_wire.validate_record_fields_loop.body
  cases hn : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorChunksExact U8) iter with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨item, next⟩
    cases item with
    | none => rfl
    | some item =>
      rcases item with ⟨index, bytes⟩
      simp only [bind_tc_ok]
      change mapResult (mapControl statusToRecord) (do
          let decoded ← AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes
          let status ← AspisR1PrefixAggregateParser.core.option.Option.ok_or decoded
            (AspisR1PrefixAggregateParser.r1_wire.Error.NonCanonical row index)
          let branch ← core.result.Result.Insts.CoreOpsTry.branch status
          match branch with
          | core.ops.control_flow.ControlFlow.Continue w => do
            let q ← AspisR1PrefixAggregateParser.field.wide_exact.WideExact.impl.c1 w
            let bad ← core.cmp.PartialEq.ne.trait_default
              AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31 q AspisR1PrefixAggregateParser.field.QM31.ZERO
            if bad then ok (done (core.result.Result.Err
              (AspisR1PrefixAggregateParser.r1_wire.Error.NonCanonical row index)))
            else ok (cont next)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let result ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame AspisR1PrefixAggregateParser.r1_wire.Error) residual
            ok (done result)) = (do
          let decoded ← AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes
          let status ← AspisR1RecordParser.core.option.Option.ok_or decoded
            (AspisR1RecordParser.r1_wire.Error.NonCanonical row index)
          let branch ← core.result.Result.Insts.CoreOpsTry.branch status
          match branch with
          | core.ops.control_flow.ControlFlow.Continue w => do
            let q ← AspisR1RecordParser.field.wide_exact.WideExact.impl.c1 w
            let bad ← core.cmp.PartialEq.ne.trait_default
              AspisR1RecordParser.field.QM31.Insts.CoreCmpPartialEqQM31 q AspisR1RecordParser.field.QM31.ZERO
            if bad then ok (done (core.result.Result.Err
              (AspisR1RecordParser.r1_wire.Error.NonCanonical row index)))
            else ok (cont next)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let result ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame AspisR1RecordParser.r1_wire.Error) residual
            ok (done result))
      rw [← from_le_bytes_agreement]
      cases hd : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes with
      | fail e => rfl
      | div => rfl
      | ok decoded =>
        cases decoded with
        | none => rfl
        | some w =>
          simp only [mapResult_ok, Option.map_some, bind_tc_ok,
            AspisR1PrefixAggregateParser.core.option.Option.ok_or,
            AspisR1RecordParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            AspisR1PrefixAggregateParser.field.wide_exact.WideExact.impl.c1,
            AspisR1RecordParser.field.wide_exact.WideExact.impl.c1,
            wideToRecord, mapResult_bind, mapResult_ite]
          have hne : core.cmp.PartialEq.ne.trait_default
              AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31
              w.c1 AspisR1PrefixAggregateParser.field.QM31.ZERO =
              core.cmp.PartialEq.ne.trait_default
                AspisR1RecordParser.field.QM31.Insts.CoreCmpPartialEqQM31
                (qmToRecord w.c1) AspisR1RecordParser.field.QM31.ZERO := by
            rw [← qm_zero_agreement]
            rfl
          rw [← hne]
          simp only [mapResult_bind, mapResult_ite, mapResult_ok,
            mapControl, statusToRecord, errorToRecord]

/-- A continued iteration consumes exactly one remaining complete chunk. -/
theorem body_cont_decreases (row : U8) (iter next : Iter)
    (h : AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body row iter =
      ok (cont next)) : next.iter.chunks.length < iter.iter.chunks.length := by
  cases hc : iter.iter.chunks with
  | nil =>
    simp only [AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorChunksExact.next, hc, bind_tc_ok] at h
    cases h
  | cons chunk chunks =>
    simp only [AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body,
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorChunksExact.next, hc, bind_tc_ok] at h
    cases ha : iter.count + 1#usize with
    | fail e => simp only [ha, bind_tc_fail] at h; cases h
    | div => simp only [ha, bind_tc_div] at h; cases h
    | ok count =>
      simp only [ha, bind_tc_ok] at h
      change (do
          let decoded ← AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes chunk
          let status ← AspisR1PrefixAggregateParser.core.option.Option.ok_or decoded
            (AspisR1PrefixAggregateParser.r1_wire.Error.NonCanonical row iter.count)
          let branch ← core.result.Result.Insts.CoreOpsTry.branch status
          match branch with
          | core.ops.control_flow.ControlFlow.Continue w => do
            let q ← AspisR1PrefixAggregateParser.field.wide_exact.WideExact.impl.c1 w
            let bad ← core.cmp.PartialEq.ne.trait_default
              AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31 q AspisR1PrefixAggregateParser.field.QM31.ZERO
            if bad then ok (done (core.result.Result.Err
              (AspisR1PrefixAggregateParser.r1_wire.Error.NonCanonical row iter.count)))
            else ok (cont ({ iter := { chunks := chunks, remainder := iter.iter.remainder }, count := count } : Iter))
          | core.ops.control_flow.ControlFlow.Break residual => do
            let result ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame AspisR1PrefixAggregateParser.r1_wire.Error) residual
            ok (done result)) = ok (cont next) at h
      cases hd : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes chunk with
      | fail e => simp only [hd, bind_tc_fail] at h; cases h
      | div => simp only [hd, bind_tc_div] at h; cases h
      | ok decoded =>
        cases decoded with
        | none =>
          simp only [hd, bind_tc_ok,
            AspisR1PrefixAggregateParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
          cases h
        | some w =>
          simp only [hd, bind_tc_ok,
            AspisR1PrefixAggregateParser.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            AspisR1PrefixAggregateParser.field.wide_exact.WideExact.impl.c1] at h
          cases hz : core.cmp.PartialEq.ne.trait_default
              AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31
              w.c1 AspisR1PrefixAggregateParser.field.QM31.ZERO with
          | fail e => simp only [hz, bind_tc_fail] at h; cases h
          | div => simp only [hz, bind_tc_div] at h; cases h
          | ok bad =>
            cases bad with
            | true => simp only [hz, bind_tc_ok, ↓reduceIte] at h; cases h
            | false =>
              simp only [hz, bind_tc_ok, ↓reduceIte] at h
              cases h
              simp only [hc, List.length_cons]
              omega

theorem validator_loop_agreement (row : U8) (iter : Iter) :
    mapResult statusToRecord
      (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop iter row) =
      AspisR1RecordParser.r1_wire.validate_record_fields_loop iter row := by
  exact loop_map statusToRecord
    (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body row)
    (AspisR1RecordParser.r1_wire.validate_record_fields_loop.body row)
    (fun it => it.iter.chunks.length) (body_agreement row)
    (body_cont_decreases row) iter

theorem validator_agreement (row : U8) (payload : Slice U8) :
    mapResult statusToRecord
      (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload) =
      AspisR1RecordParser.r1_wire.validate_record_fields row payload := by
  unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields
    AspisR1RecordParser.r1_wire.validate_record_fields
  simp only [mapResult_bind, validator_loop_agreement]

end AspisR1.ExtractedPrefixRecordAgreement

#print axioms AspisR1.ExtractedPrefixRecordAgreement.row_shape_agreement
#print axioms AspisR1.ExtractedPrefixRecordAgreement.body_agreement

#print axioms AspisR1.ExtractedPrefixRecordAgreement.body_cont_decreases
#print axioms AspisR1.ExtractedPrefixRecordAgreement.validator_loop_agreement
#print axioms AspisR1.ExtractedPrefixRecordAgreement.validator_agreement
