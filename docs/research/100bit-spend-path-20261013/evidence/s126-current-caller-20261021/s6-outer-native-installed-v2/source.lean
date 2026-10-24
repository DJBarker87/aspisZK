import S6OuterNativeReturnsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterNativeInstalled
open AspisS6OuterCarrierBridge AspisS6OuterNativeOps
abbrev Statement := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Error := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

/-- Concrete instance of the existing extracted outer source cut, with the
complete native input/error carriers. No free child operations remain. -/
def encode (statement : Statement) : Result (core.result.Result (Array U8 1880#usize) Error) :=
  resultMap (rustMapError toPoolV1PairForestTerminalFormatErrorV1)
    (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
      nativeOps (fromPoolV1PairForestTerminalStatementV1 statement))

theorem common_return (statement : Statement) :
    resultMap toPoolV1PairForestTerminalCommonV1
      (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
        (fromPoolV1PairForestTerminalStatementV1 statement)) =
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement := by
  cases statement <;> simp only [fromPoolV1PairForestTerminalStatementV1,
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common,
    resultMap,to_fromPoolV1PairForestTerminalCommonV1]

theorem private_tag
    (common : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (payload : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    (do let kind ← AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
        (fromPoolV1PairForestTerminalStatementV1 (.PrivateTransfer common payload))
        ok (read_discriminant kind : U8))=ok 1#u8 := by rfl

theorem withdrawal_tag
    (common : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (payload : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    (do let kind ← AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.transition_kind
        (fromPoolV1PairForestTerminalStatementV1 (.Withdrawal common payload))
        ok (read_discriminant kind : U8))=ok 2#u8 := by rfl

#print axioms encode
#print axioms common_return
#print axioms private_tag
#print axioms withdrawal_tag
end AspisS6OuterNativeInstalled
