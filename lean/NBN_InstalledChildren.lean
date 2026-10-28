import NBN_StatementResult
import S6OuterNativeOpsV1
set_option autoImplicit false
noncomputable section
namespace NBN_InstalledChildren
open Aeneas Aeneas.Std Result
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge

theorem validator (s : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    nativeOps.validate s = resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1)
      (NBN_StatementResult.result (toPoolV1PairForestTerminalStatementV1 s)) := by
  change resultMap _ (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 _) = _
  rw [NBN_StatementResult.source]

theorem late (s : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (output : Slice U8) :
    nativeOps.late s output = resultMap
      (fun result => (rustMapError fromPoolV1PairLatePublicStatementErrorV1 result.1,result.2))
      (if output.length ≠ 1520 then ok (.Err .WrongLength,output)
      else if U64.checked_add (toPoolV1PairLatePublicStatementV1 s).live_snapshot.next_pair_index 1#u64 ≠
          some (toPoolV1PairLatePublicStatementV1 s).candidate_afterstate.next_pair_index then
        ok (.Err .AfterstateIndexMismatch,output)
      else ok (NBN_LateTail.status (toPoolV1PairLatePublicStatementV1 s),
        NBN_LateTail.value (toPoolV1PairLatePublicStatementV1 s) NBN_LateResult.header)) := by
  change resultMap _ (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 _ output) = _
  rw [NBN_LateResult.source]

#print axioms validator
#print axioms late
end NBN_InstalledChildren
