import AspisR1TerminalDecoder.Funs
import R1Z.PV_W_IfLaws
import R1Z.PV_RJDec_ParserR10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ParserR16
open Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws
variable [ProverRwFull.ExternalTypes]

def program
  (common : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (payment : Slice Std.U8) :
  P (core.result.Result pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) := do
  let r ← R1Z.PV_RJDec_ParserR10.program payment
  let r1 ← invoke "core.result.Result.map_err" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.map_err (BuiltinFnOnce pool_v1.payment_relation.PoolV1PaymentStatementFormatError pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) r (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.PaymentConstructor))
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r1)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    pure (core.result.Result.Ok (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal common val))
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ProverRwFull.ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 (core.convert.FromSame pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) residual)

theorem source (ops : ProverRwFull.ExternalFuns)
  (common : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (payment : Slice Std.U8) :
  erase ops (program common payment) =
    pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1 common payment := by
  unfold program pool_v1.pair_forest_terminal.decode_withdrawal_statement_boxed_v1
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact R1Z.PV_RJDec_ParserR10.source ops payment
  · intro r
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro r1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          rfl
        | Break residual =>
          exact erase_invoke ops _ _

#print axioms source
end R1Z.PV_RJDec_ParserR16
