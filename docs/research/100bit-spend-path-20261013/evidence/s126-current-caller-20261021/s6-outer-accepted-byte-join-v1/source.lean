import S6OuterAcceptedCalleesV1
import S6OuterByteLayoutV1
import S6NativeForestDecodedLayoutV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterAcceptedByteJoin
open AspisS6OuterCarrierBridge AspisS6OuterNativeOps
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

theorem common_contents (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))
    (common : PoolV1PairForestTerminalCommonV1)
    (common_run : PoolV1PairForestTerminalStatementV1.common statement=ok common) :
    AspisS6OuterByteLayout.common_prefix (fromPoolV1PairForestTerminalCommonV1 common)
      (AspisS6NativeForestDecode.statement_tag statement)=bytes.val.take 144 := by
  rcases AspisS6NativeForestDecode.accepted_frames bytes statement accepted with
    ⟨⟨raw,raw_bytes,header⟩,⟨reached,reached_run,fields⟩,_⟩
  rw [common_run] at reached_run
  cases reached_run
  have same : AspisS6OuterByteLayout.common_prefix (fromPoolV1PairForestTerminalCommonV1 common)
      (AspisS6NativeForestDecode.statement_tag statement)=AspisS6NativeForestDecode.common_prefix statement common := by rfl
  rw [same]
  exact AspisS6NativeForestDecode.common_prefix_contents bytes statement common raw raw_bytes header fields

theorem late_contents (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))
    (common : PoolV1PairForestTerminalCommonV1)
    (common_run : PoolV1PairForestTerminalStatementV1.common statement=ok common)
    (initial updated : Slice U8) (size : initial.length=1520)
    (run : nativeOps.late (fromPoolV1PairLatePublicStatementV1 common.lane_transition) initial=ok (.Ok (),updated)) :
    updated.val=List.slice 144 1664 bytes.val := by
  obtain ⟨reached,correct,reached_run,correct_run,contents⟩ :=
    AspisS6OuterAcceptedCallees.late_from_decode bytes statement accepted initial size
  rw [common_run] at reached_run
  cases reached_run
  rw [run] at correct_run
  cases correct_run
  exact contents

theorem transfer_contents (bytes : Slice U8) (common : PoolV1PairForestTerminalCommonV1)
    (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok (.PrivateTransfer common value)))
    (encoded : Array U8 216#usize)
    (run : nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 value)=ok (.Ok encoded)) :
    encoded.val=bytes.val.drop 1664 := by
  obtain ⟨correct,correct_run,contents⟩ := AspisS6OuterAcceptedCallees.payment_from_decode bytes (.PrivateTransfer common value) accepted
  rw [run] at correct_run
  cases correct_run
  exact contents

theorem withdrawal_contents (bytes : Slice U8) (common : PoolV1PairForestTerminalCommonV1)
    (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok (.Withdrawal common value)))
    (encoded : Array U8 216#usize)
    (run : nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 value)=ok (.Ok encoded)) :
    encoded.val=bytes.val.drop 1664 := by
  obtain ⟨correct,correct_run,contents⟩ := AspisS6OuterAcceptedCallees.payment_from_decode bytes (.Withdrawal common value) accepted
  rw [run] at correct_run
  cases correct_run
  exact contents

#print axioms common_contents
#print axioms late_contents
#print axioms transfer_contents
#print axioms withdrawal_contents
end AspisS6OuterAcceptedByteJoin
