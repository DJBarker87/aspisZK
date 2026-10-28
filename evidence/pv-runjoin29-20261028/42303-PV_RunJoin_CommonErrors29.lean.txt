import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CommonErrors29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Exact first-error paths of the pinned extracted public validator. -/
def Path (common : pool_v1.payment_relation.CommonPublicV1)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : Prop :=
  let a := Array.repeat 32#usize 0#u8
  ∃ b, (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.pool a) = ok b ∧
  if b
  then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
  else
    let a1 := Array.repeat 32#usize 0#u8
    ∃ b1, (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.deployment_domain a1) = ok b1 ∧
    if b1
    then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
    else ∃ i, (pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY) = ok i ∧
         if common.anchor_sequence > i
         then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
         else ∃ b2, (pool_v1.payment_relation.digest_is_canonical common.anchor_root) = ok b2 ∧
              if b2
              then ∃ b3, (pool_v1.payment_relation.digest_is_canonical common.nullifier) = ok b3 ∧
                   if b3
                   then let i1 := common.asset_id
                        if i1 >= aspis_core.field.P
                        then (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
                        else False
                   else (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)
              else (ok (.Err pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest) : Result (core.result.Result Unit pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) = ok (.Err error)

theorem error_iff (common : pool_v1.payment_relation.CommonPublicV1)
    (error : pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    pool_v1.payment_relation.validate_common common = ok (.Err error) ↔ Path common error := by
  rw [eq_wp]
  unfold pool_v1.payment_relation.validate_common Path
  simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,ok_ne_err,residual_eq_wp,Result.ok.injEq])
#print axioms error_iff
end R1Z.PV_RunJoin_CommonErrors29
