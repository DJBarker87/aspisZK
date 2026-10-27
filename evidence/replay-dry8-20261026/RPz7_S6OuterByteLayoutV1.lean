import S6OuterWriteFramesV1
import RPz7_S6OuterNativeInstalledV1
import RPz7_S6NativePaymentCommonContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterByteLayout
open AspisS6FullForestEncoderNamed.aspis_statement.pool_v1

def common_prefix (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (tag : U8) : List U8 :=
  pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val++
    [pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,tag,format.POOL_V1_DIGEST_ENCODING_VERSION,common.output_lane]++
    common.master_account.val++common.checkpoint_account.val++common.selected_lane_account.val++
    (core.num.U64.to_le_bytes common.checkpoint_sequence).val++
    AspisS6SourceCodec.DigestContents.chunks common.historical_global_anchor

theorem common_length (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (tag : U8) :
    (common_prefix common tag).length=144 := by
  simp only [common_prefix,List.length_append,List.length_cons,List.length_nil,
    pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.property,
    common.master_account.property,common.checkpoint_account.property,common.selected_lane_account.property,
    (core.num.U64.to_le_bytes common.checkpoint_sequence).property,
    AspisS6NativePaymentContents.digest_chunks_length]
  decide

def prepared_header (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (tag : U8) : List U8 :=
  (((((List.replicate 1880 0#u8).setSlice! 0 pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val).set
    4 pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION).set 5 tag).set
    6 format.POOL_V1_DIGEST_ENCODING_VERSION).set 7 common.output_lane

theorem assembled (common : pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (tag : U8)
    (late payment : List U8) (hl : late.length=1520) (hp : payment.length=216) :
    (((((((prepared_header common tag).setSlice! 8 common.master_account.val).setSlice! 40 common.checkpoint_account.val).setSlice!
      72 common.selected_lane_account.val).setSlice! 104 (core.num.U64.to_le_bytes common.checkpoint_sequence).val).setSlice!
      112 (AspisS6SourceCodec.DigestContents.chunks common.historical_global_anchor)).setSlice! 144 late).setSlice! 1664 payment =
      (common_prefix common tag++late)++payment := by
  unfold prepared_header
  rw [AspisS6SliceFrame.forest_header_writes _ pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.property]
  rw [AspisS6SliceFrame.forest_common_writes]
  · exact AspisS6SliceFrame.forest_payload_writes _ _ late payment (common_length common tag) hl hp
  · simp only [List.length_append,List.length_cons,List.length_nil,
      pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.property]
    decide
  · exact common.master_account.property
  · exact common.checkpoint_account.property
  · exact common.selected_lane_account.property
  · exact (core.num.U64.to_le_bytes common.checkpoint_sequence).property
  · exact AspisS6NativePaymentContents.digest_chunks_length _

#print axioms common_length
#print axioms assembled
end AspisS6OuterByteLayout
