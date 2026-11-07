import NMT_345Dec_T1
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT2 (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
def fromT2 (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
@[simp] theorem toT2_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromT2 (toT2 x) = x := by
 cases x <;> simp [toT2,fromT2]
#print axioms toT2_inverse
@[simp] theorem fromT2_inverse (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toT2 (fromT2 x) = x := by
 cases x <;> simp [fromT2,toT2]
#print axioms fromT2_inverse
end NMT_345Dec
