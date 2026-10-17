import AspisR1TerminalDecoder.Funs
import R1M31ParserArray
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualM31ParserBridge
open Aeneas Aeneas.Std Result

theorem actual_m31_parser_eq_retained (bytes : Array U8 4#usize) :
    AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes bytes =
      AspisR1M31Parser.field.M31.from_le_bytes bytes := by
  simp [AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes,
    AspisR1TerminalDecoder.aspis_core.field.P,
    AspisR1M31Parser.field.M31.from_le_bytes,
    AspisR1M31Parser.field.P]

#print axioms actual_m31_parser_eq_retained
end AspisR1PairForestLaneEncoderTailActualM31ParserBridge
