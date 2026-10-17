import LaneEncoderActualM31ParserBridge
import LaneEncoderM31CodecRoundtrip
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailM31ParserAcceptEncoded
open Aeneas Aeneas.Std Result

theorem actual_parser_accepts_encoded (value : U32)
    (hcanonical : value.val < 2147483647) :
    AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (core.num.U32.to_le_bytes value) = .ok (some value) := by
  rw [AspisR1PairForestLaneEncoderTailActualM31ParserBridge.actual_m31_parser_eq_retained]
  unfold AspisR1M31Parser.field.M31.from_le_bytes
  rw [AspisR1PairForestLaneEncoderTailM31Codec.u32_from_to_le]
  simp only [lift, bind_tc_ok]
  have hnot : ¬ 2147483647 ≤ value.val := by omega
  simp [AspisR1M31Parser.field.P, hnot]

#print axioms actual_parser_accepts_encoded
end AspisR1PairForestLaneEncoderTailM31ParserAcceptEncoded
