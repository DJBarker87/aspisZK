import NBN_EncoderDomains
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderRejection
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem source (s : Statement) (e : NBN_StatementResult.Error)
    (reject : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err e)) :
    AspisS6OuterNativeInstalled.encode s = ok (.Err e) := by
  have v : nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 s) =
      ok (.Err (fromPoolV1PairForestTerminalFormatErrorV1 e)) := by
    rw [validate_call,reject]
    rfl
  unfold AspisS6OuterNativeInstalled.encode
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
  rw [v]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp [resultMap,rustMapError,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,to_fromPoolV1PairForestTerminalFormatErrorV1]

#print axioms source
end NBN_EncoderRejection
