import ExtractedPrefixRecordAgreement

/-! Exact final Prefix-E versus record-parser-F parsing, using the explicit
field/validator/error maps. No assumed old-parser success is introduced. -/
namespace AspisR1.ExtractedPrefixParserAgreement
open Aeneas Aeneas.Std Result
open ExtractedPrefixFieldAgreement ExtractedPrefixRecordAgreement

theorem bind_mapResult {α β γ : Type} (f : α → β)
    (m : Result α) (k : β → Result γ) :
    (mapResult f m >>= k) = (m >>= fun value => k (f value)) := by
  cases m <;> rfl

private theorem after_validation (payload : Slice U8)
    (status : core.result.Result Unit AspisR1PrefixAggregateParser.r1_wire.Error) :
    mapResult statusToRecord (do
      let branch ← core.result.Result.Insts.CoreOpsTry.branch status
      match branch with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok payload)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Slice U8) (core.convert.FromSame AspisR1PrefixAggregateParser.r1_wire.Error) residual) = (do
      let branch ← core.result.Result.Insts.CoreOpsTry.branch (statusToRecord status)
      match branch with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok payload)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Slice U8) (core.convert.FromSame AspisR1RecordParser.r1_wire.Error) residual) := by
  cases status <;> rfl

/-- Exact equality includes ordinary errors and Aeneas runtime failure/div. -/
theorem parse_record_agreement (row : U8) (frame : Slice U8) :
    mapResult statusToRecord
      (AspisR1PrefixAggregateParser.r1_wire.parse_record row frame) =
      AspisR1RecordParser.r1_wire.parse_record row frame := by
  unfold AspisR1PrefixAggregateParser.r1_wire.parse_record
    AspisR1RecordParser.r1_wire.parse_record
  rw [← row_shape_agreement]
  cases hs : AspisR1PrefixAggregateParser.r1_wire.row_shape row with
  | fail e => rfl
  | div => rfl
  | ok shape =>
    cases shape with
    | none => rfl
    | some pair =>
      rcases pair with ⟨tag, size⟩
      simp only [bind_tc_ok,
        AspisR1PrefixAggregateParser.core.option.Option.ok_or,
        AspisR1RecordParser.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch]
      simp only [mapResult_bind, mapResult_ite, mapResult_ok,
        statusToRecord, errorToRecord, ← validator_agreement,
        bind_mapResult, after_validation]

theorem parse_record_success (row : U8) (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload)) :
    AspisR1RecordParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload) := by
  rw [← parse_record_agreement, h]
  rfl

end AspisR1.ExtractedPrefixParserAgreement

#print axioms AspisR1.ExtractedPrefixParserAgreement.parse_record_agreement
#print axioms AspisR1.ExtractedPrefixParserAgreement.parse_record_success
