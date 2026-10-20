import BinWirePublicLengths
import ExtractedTerminalDecoderSuccess

/-! Length separation for success of the retained extracted ASF8 decoder.
The outer decoder's guards are unchanged in the adopted source; no account
reachability, reconstructed-statement binding or Rust execution is assumed. -/
set_option autoImplicit false
namespace AspisR1.BinWireEnvelopeLengths
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

theorem decoded_asf8_length (bs : Slice U8) (out : PoolV1PairForestTerminalStatementV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bs = ok (.Ok out)) :
    bs.val.length = 1880 :=
  (AspisR1TerminalDecoder.DecoderSuccess.decode_success bs out h).2.1

theorem decoded_asf8_ne_node (bs : Slice U8) (out : PoolV1PairForestTerminalStatementV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bs = ok (.Ok out))
    (toByte : U8 → BinMerkle32Path.Byte) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠ bs.val.map toByte := by
  apply BinWirePublicLengths.fixed_public_ne_node
  left
  simpa only [List.length_map] using decoded_asf8_length bs out h

#print axioms decoded_asf8_length
#print axioms decoded_asf8_ne_node
end AspisR1.BinWireEnvelopeLengths
