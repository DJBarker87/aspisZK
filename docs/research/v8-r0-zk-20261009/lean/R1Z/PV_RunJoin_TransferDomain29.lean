import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_ControlDomain28
import R1Z.PV_RunJoin_RejectionProof28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TransferDomain29
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28

/-- Exact operational success path of the pinned extracted statement validator.
Every callee result and first-error branch remains explicit. -/
def Path (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : Prop :=
  ∃ cpv, (pool_v1.payment_relation.transfer_common public1) = ok cpv ∧
  ∃ r, (pool_v1.payment_relation.validate_common cpv) = ok r ∧
  ∃ cf, (core.result.Result.Insts.CoreOpsTry.branch r) = ok cf ∧
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => ∃ b, (pool_v1.payment_relation.digest_is_canonical public1.recipient_commitment) = ok b ∧
                                                    if b
                                                    then ∃ b1, (pool_v1.payment_relation.digest_is_canonical public1.change_commitment) = ok b1 ∧
                                                         if b1
                                                         then True
                                                         else False
                                                    else False
  | core.ops.control_flow.ControlFlow.Break residual => False

theorem success_iff (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    (∃ u, pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 public1 = ok (.Ok u)) ↔ Path public1 := by
  rw [success_wp]
  unfold pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp])
#print axioms success_iff
end R1Z.PV_RunJoin_TransferDomain29
