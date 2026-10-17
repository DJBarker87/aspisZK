import LaneEncoderActualDigestChunkParserV2e
import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import LaneEncoderChunkArrayEquality
import AspisR1TerminalDecoder.Funs
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser
open Aeneas Aeneas.Std Result

theorem actual_m31_parser_accepts_encoded_field_window
    (out : Array U8 32#usize) (offset : Nat)
    (hoff : offset + 4 ≤ 32)
    (value : AspisR1PairForestLaneEncoderTailSourceCut.M31)
    (fieldBytes : Array U8 4#usize)
    (hfield : AspisR1PairForestLaneEncoderTailSourceCut.M31.to_le_bytes value = .ok fieldBytes)
    (hwindow : ∀ k : Nat, k < 4 → out.val[offset + k]? = fieldBytes.val[k]?)
    (hcanonical : value.val < 2147483647) :
    AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk out offset hoff) =
        .ok (some value) := by
  have hfieldBytes : fieldBytes = core.num.U32.to_le_bytes value := by
    have h := hfield
    change Result.ok (core.num.U32.to_le_bytes value) = Result.ok fieldBytes at h
    exact Result.ok.inj h.symm
  apply AspisR1PairForestLaneEncoderTailActualDigestChunkParser.actual_m31_parser_accepts_window_getElem? out offset hoff value ?_ hcanonical
  intro k hk
  have hw := hwindow k hk
  rw [hfieldBytes] at hw
  exact hw

#print axioms actual_m31_parser_accepts_encoded_field_window
end AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser
