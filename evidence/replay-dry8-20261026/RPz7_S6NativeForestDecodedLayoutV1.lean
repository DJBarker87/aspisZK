import RPz7_S6NativeForestAcceptedFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

def common_prefix (statement : PoolV1PairForestTerminalStatementV1)
    (common : PoolV1PairForestTerminalCommonV1) : List U8 :=
  POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val++
    [POOL_V1_PAIR_FOREST_TERMINAL_VERSION,statement_tag statement,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,common.output_lane]++
    common.master_account.val++common.checkpoint_account.val++common.selected_lane_account.val++
    (core.num.U64.to_le_bytes common.checkpoint_sequence).val++
    AspisS6SourceCodec.DigestContents.chunks common.historical_global_anchor

theorem common_prefix_length (statement : PoolV1PairForestTerminalStatementV1)
    (common : PoolV1PairForestTerminalCommonV1) : (common_prefix statement common).length=144 := by
  simp only [common_prefix,List.length_append,List.length_cons,List.length_nil,
    POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.property,common.master_account.property,
    common.checkpoint_account.property,common.selected_lane_account.property,
    (core.num.U64.to_le_bytes common.checkpoint_sequence).property,
    AspisS6NativePaymentContents.digest_chunks_length]
  decide

theorem common_prefix_contents (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (common : PoolV1PairForestTerminalCommonV1) (raw : Array U8 1880#usize)
    (rawbytes : raw.val=bytes.val) (header : header_frame raw statement)
    (fields : common_frame bytes common) : common_prefix statement common=bytes.val.take 144 := by
  rcases header with ⟨magic,h4,h5,h6⟩
  rcases fields with ⟨⟨lane_raw,lane_bytes,lane⟩,master,checkpoint,selected,sequence,⟨anchor,anchor_run,anchor_bytes⟩,_⟩
  have lane_eq : lane_raw=raw := Subtype.ext (lane_bytes.trans rawbytes.symm)
  rw [lane_eq] at lane
  have hm : raw.val.take 4=POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val := by simpa [List.slice] using magic
  have head := AspisS6SliceFrame.header_eight raw.val (by rw [raw.property]; decide)
  rw [hm,h4,h5,h6,←lane] at head
  rw [rawbytes] at head
  have anchor_contents := (AspisS6NativePaymentContents.encoded_digest_chunks common.historical_global_anchor anchor anchor_run).trans anchor_bytes
  unfold common_prefix
  rw [←head,master,checkpoint,selected,sequence,anchor_contents]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 8 40 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 40 72 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 72 104 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 104 112 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 112 144 (by decide)]

#print axioms common_prefix_length
#print axioms common_prefix_contents
end AspisS6NativeForestDecode
