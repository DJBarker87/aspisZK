import RawJ_SampleRead
import S1SemanticFinishModelV1
set_option autoImplicit false
namespace AspisR1.RawJ_RecordPayload
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem framed (p : r1_wire.Prefix) (row : U8) (record : r1_wire.ValidatedRecord)
    (payload : Slice U8) (root : Array U8 32#usize)
    (valid : p.validated_record row = ok (.Ok record))
    (read : FinishModel.payload p row = ok (.Ok payload)) (bytes : payload.val = root.val) :
    ∃ pre : List U8, record.framed.val = pre ++ root.val := by
  unfold r1_wire.Prefix.validated_record at valid
  unfold FinishModel.payload at read
  cases call : p.record row with
  | fail e => simp only [call,bind_tc_fail] at valid; cases valid
  | div => simp only [call,bind_tc_div] at valid; cases valid
  | ok result => cases result with
    | Err e => simp [call,core.result.Result.Insts.CoreOpsTry.branch] at valid
    | Ok frame =>
      simp only [call,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at valid read
      have same : ({row,framed:=frame} : r1_wire.ValidatedRecord) = record :=
        core.result.Result.Ok.inj (Result.ok.inj valid)
      subst record
      unfold core.slice.index.Slice.index core.slice.index.SliceIndexRangeFromUsizeSlice.index at read
      split at read
      · have eq : frame.val.drop 5 = payload.val := by
          have eq := core.result.Result.Ok.inj (Result.ok.inj read)
          exact congrArg Slice.val eq
        refine ⟨frame.val.take 5,?_⟩
        rw [← bytes,← eq]
        exact (List.take_append_drop 5 frame.val).symm
      · cases read

#print axioms framed
end AspisR1.RawJ_RecordPayload
