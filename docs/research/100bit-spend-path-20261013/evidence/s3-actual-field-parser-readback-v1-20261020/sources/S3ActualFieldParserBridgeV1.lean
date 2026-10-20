import S3ActualFieldOpsComplete
import WeightsFieldSuccess
import FinishFieldSelectorAdapterV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

private theorem bind_success_parser_bridge {A B : Type} (m : Result A)
    (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful field callback in the actual loop owner comes from a successful
record parser call on the exact `i*32 .. (i+1)*32` byte slice.  This keeps the
parsed record value and the output's coordinate conversion in one witness. -/
theorem decodeField_success_parser_readback
    (bytes : Slice Std.U8) (i : Std.Usize) (out : S)
    (h : decodeField bytes i = .ok out) :
    ∃ (raw : AspisR1RecordParser.field.wide_exact.WideExact)
      (start next finish : Std.Usize) (selected : Slice Std.U8),
      AspisR1WeightsFieldCurrent.weights.field
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i = .ok raw ∧
      (i * 32#usize : Result Usize) = .ok start ∧
      (i + 1#usize : Result Usize) = .ok next ∧
      (next * 32#usize : Result Usize) = .ok finish ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := start, «end» := finish } = .ok selected ∧
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
        .ok (some raw) ∧
      out = finishToS
        (AspisR1CurrentWide.Proof.recordWideToFinish raw) := by
  unfold decodeField at h
  obtain ⟨finishValue, hfinish, hmap⟩ :=
    bind_success_parser_bridge
      (AspisR1CurrentWide.Proof.finishField bytes i)
      (fun x => .ok (finishToS x)) out h
  have hout : finishToS finishValue = out := Result.ok.inj hmap
  unfold AspisR1CurrentWide.Proof.finishField at hfinish
  obtain ⟨raw, hraw, hrecord⟩ :=
    bind_success_parser_bridge
      (AspisR1WeightsFieldCurrent.weights.field
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i)
      (fun x => .ok (AspisR1CurrentWide.Proof.recordWideToFinish x)) finishValue hfinish
  have hrecordValue : AspisR1CurrentWide.Proof.recordWideToFinish raw = finishValue :=
    Result.ok.inj hrecord
  obtain ⟨start, next, finish, selected, hi, hn, hf, hs, hdecode⟩ :=
    AspisR1WeightsFieldCurrent.WeightsFieldSuccess.checked_slice_decode
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i raw hraw
  refine ⟨raw, start, next, finish, selected, hraw, hi, hn, hf, hs, hdecode, ?_⟩
  calc
    out = finishToS finishValue := hout.symm
    _ = finishToS (AspisR1CurrentWide.Proof.recordWideToFinish raw) :=
      (congrArg finishToS hrecordValue).symm

#print axioms decodeField_success_parser_readback

end AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
