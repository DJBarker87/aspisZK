import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_BranchDomain28
import R1Z.PV_RunJoin_ControlDomain28
import R1Z.PV_RunJoin_RejectionProof28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CommonDomain29
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28

/-- Exact operational success path of the pinned extracted statement validator.
Every callee result and first-error branch remains explicit. -/
def Path (common : pool_v1.payment_relation.CommonPublicV1) : Prop :=
  let a := Array.repeat 32#usize 0#u8
  ∃ b, (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.pool a) = ok b ∧
  if b
  then False
  else
    let a1 := Array.repeat 32#usize 0#u8
    ∃ b1, (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.deployment_domain a1) = ok b1 ∧
    if b1
    then False
    else ∃ i, (pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY) = ok i ∧
         if common.anchor_sequence > i
         then False
         else ∃ b2, (pool_v1.payment_relation.digest_is_canonical common.anchor_root) = ok b2 ∧
              if b2
              then ∃ b3, (pool_v1.payment_relation.digest_is_canonical common.nullifier) = ok b3 ∧
                   if b3
                   then let i1 := common.asset_id
                        if i1 >= aspis_core.field.P
                        then False
                        else True
                   else False
              else False

theorem success_iff (common : pool_v1.payment_relation.CommonPublicV1) :
    (∃ u, pool_v1.payment_relation.validate_common common = ok (.Ok u)) ↔ Path common := by
  rw [success_wp]
  unfold pool_v1.payment_relation.validate_common Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp])
#print axioms success_iff
end R1Z.PV_RunJoin_CommonDomain29
