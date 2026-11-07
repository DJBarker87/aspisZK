import NNG_Transport_T3
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT4 (x : NNG_verify_finish.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
def fromT4 (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NNG_verify_finish.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
@[simp] theorem toT4_inverse (x : NNG_verify_finish.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromT4 (toT4 x)=x := by
 cases x <;> simp [toT4,fromT4]
#print axioms toT4_inverse
@[simp] theorem fromT4_inverse (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toT4 (fromT4 x)=x := by
 cases x <;> simp [fromT4,toT4]
#print axioms fromT4_inverse
end AspisR1.NNG_Transport
