import NBG_PaymentChecks
set_option autoImplicit false
noncomputable section
namespace NBG_PaymentValidators
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBG_PaymentChecks
abbrev T := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := pool_v1.payment_relation.PoolV1WithdrawalPublicV1

def tc (p : T) : C :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id }
def wc (p : W) : C :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id }

def transfer (p : T) : core.result.Result Unit E :=
  match common (tc p) with
  | .Err e => .Err e
  | .Ok () => if !canonical p.recipient_commitment || !canonical p.change_commitment
      then .Err .NonCanonicalDigest else .Ok ()

theorem transfer_result (p : T) :
    pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 p =
      ok (transfer p) := by
  simp only [pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1,
    NBG_Atomic.transfer_projection,bind_tc_ok]
  fold tc
  rw [common_result,bind_tc_ok]
  cases h : common (tc p) with
  | Err e => simp [transfer,h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok value => cases value; simp [transfer,h,canonical_result,
      core.result.Result.Insts.CoreOpsTry.branch]
                repeat' split
                all_goals simp_all

theorem value_limit : spend.VALUE_LIMIT = ok 1073741824#u32 := by
  unfold spend.VALUE_LIMIT
  rfl

def withdrawal (p : W) : core.result.Result Unit E :=
  match common (wc p) with
  | .Err e => .Err e
  | .Ok () => if p.amount.val = 0 ∨ p.amount.val >= 1073741824
      then .Err .InvalidWithdrawalAmount
      else if zero p.destination_token_account then .Err .InvalidDestination
      else if !canonical p.change_commitment then .Err .NonCanonicalDigest
      else .Ok ()

theorem withdrawal_result (p : W) :
    pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p =
      ok (withdrawal p) := by
  simp only [pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1,
    NBG_Atomic.withdrawal_projection,bind_tc_ok]
  fold wc
  rw [common_result,bind_tc_ok]
  cases h : common (wc p) with
  | Err e => simp [withdrawal,h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok value => cases value; simp [withdrawal,h,canonical_result,zero_result,value_limit,
      core.result.Result.Insts.CoreOpsTry.branch]
                repeat' split
                all_goals simp_all <;> scalar_tac

#print axioms transfer_result
#print axioms value_limit
#print axioms withdrawal_result
end NBG_PaymentValidators
