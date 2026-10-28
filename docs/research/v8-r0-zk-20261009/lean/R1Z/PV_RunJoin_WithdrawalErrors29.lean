import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WithdrawalErrors29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Exact first-error paths of the pinned extracted public validator. -/
def Path (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : Prop :=
  ∃ cpv, (pool_v1.payment_relation.withdrawal_common public1) = ok cpv ∧
  ∃ r, (pool_v1.payment_relation.validate_common cpv) = ok r ∧
  ∃ cf, (core.result.Result.Insts.CoreOpsTry.branch r) = ok cf ∧
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => if public1.amount = 0#u32
                                                    then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
                                                    else ∃ i, (spend.VALUE_LIMIT) = ok i ∧
                                                         if public1.amount >= i
                                                         then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
                                                         else let a := Array.repeat 32#usize 0#u8
                                                              ∃ b, (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 public1.destination_token_account a) = ok b ∧
                                                              if b
                                                              then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
                                                              else ∃ b1, (pool_v1.payment_relation.digest_is_canonical public1.change_commitment) = ok b1 ∧
                                                                   if b1
                                                                   then False
                                                                   else (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
  | core.ops.control_flow.ControlFlow.Break residual => (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual) = ok (.Err error)

theorem error_iff (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 public1 = ok (.Err error) ↔ Path public1 error := by
  rw [eq_wp]
  unfold pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 Path
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq])
#print axioms error_iff
end R1Z.PV_RunJoin_WithdrawalErrors29
