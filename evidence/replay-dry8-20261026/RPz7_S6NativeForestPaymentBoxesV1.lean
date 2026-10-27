import RPz7_S6NativeForestDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

@[step] theorem transfer_box_spec (common : PoolV1PairForestTerminalCommonV1) (bytes : Slice U8) :
    decode_transfer_statement_boxed_v1 common bytes ⦃ result => ∀ statement,
      result=core.result.Result.Ok statement →
      ∃ value, statement=PoolV1PairForestTerminalStatementV1.PrivateTransfer common value ∧
        pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes=ok (core.result.Result.Ok value) ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativePaymentDecode.transfer_total bytes
  apply exists_imp_spec
  cases result with
  | Ok value =>
    refine ⟨core.result.Result.Ok (PoolV1PairForestTerminalStatementV1.PrivateTransfer common value),?_,?_⟩
    · simp [decode_transfer_statement_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,core.result.Result.Insts.CoreOpsTry.branch]
    · intro statement eq; cases eq; exact ⟨value,rfl,run⟩
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairForestTerminalFormatErrorV1.Payment error),?_,?_⟩
    · simp [decode_transfer_statement_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
        PoolV1PairForestTerminalFormatErrorV1.PaymentConstructor,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame]
    · intro statement eq; cases eq

#print axioms transfer_box_spec

@[step] theorem withdrawal_box_spec (common : PoolV1PairForestTerminalCommonV1) (bytes : Slice U8) :
    decode_withdrawal_statement_boxed_v1 common bytes ⦃ result => ∀ statement,
      result=core.result.Result.Ok statement →
      ∃ value, statement=PoolV1PairForestTerminalStatementV1.Withdrawal common value ∧
        pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes=ok (core.result.Result.Ok value) ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativePaymentDecode.withdrawal_total bytes
  apply exists_imp_spec
  cases result with
  | Ok value =>
    refine ⟨core.result.Result.Ok (PoolV1PairForestTerminalStatementV1.Withdrawal common value),?_,?_⟩
    · simp [decode_withdrawal_statement_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,core.result.Result.Insts.CoreOpsTry.branch]
    · intro statement eq; cases eq; exact ⟨value,rfl,run⟩
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairForestTerminalFormatErrorV1.Payment error),?_,?_⟩
    · simp [decode_withdrawal_statement_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
        PoolV1PairForestTerminalFormatErrorV1.PaymentConstructor,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame]
    · intro statement eq; cases eq

#print axioms withdrawal_box_spec

@[step] theorem validator_graph (statement : PoolV1PairForestTerminalStatementV1) :
    validate_pool_v1_pair_forest_terminal_statement_v1 statement
      ⦃ result => validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok result ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeForestTotal.validate_total statement
  apply exists_imp_spec
  exact ⟨result,run,run⟩

#print axioms validator_graph
end AspisS6NativeForestDecode
