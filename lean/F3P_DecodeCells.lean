import F3N_PreparedCells
import AspisR1DecodeKFullSuccessIndexedParser
set_option autoImplicit false
namespace AspisR1.F3P_DecodeCells
open Aeneas Aeneas.Std Result

theorem source {n : Usize} (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (offset : Usize) (out : Array AspisS1ExtractedRoundChildren.MainQM n)
    (success : AspisS1ExtractedRoundChildren.decodeMain n r offset=ok (.Ok out)) :
    ∃ decoded : Array AspisS1ExtractedRoundChildren.DecodeQM n,
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n
        (AspisS1ExtractedRoundChildren.recordToDecoder r) offset=ok (.Ok decoded) ∧
      AspisS1ExtractedRoundChildren.decoderArrayToMain decoded=out := by
  unfold AspisS1ExtractedRoundChildren.decodeMain at success
  cases h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n
      (AspisS1ExtractedRoundChildren.recordToDecoder r) offset with
  | fail e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at success;cases success
  | div => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at success;cases success
  | ok value =>
    cases value with
    | Err e => simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at success;cases success
    | Ok decoded =>
      simp only [h,AspisS1ExtractedRoundChildren.decoderResultToMain] at success
      exact ⟨decoded,rfl,core.result.Result.Ok.inj (Result.ok.inj success)⟩

#print axioms source
end AspisR1.F3P_DecodeCells
