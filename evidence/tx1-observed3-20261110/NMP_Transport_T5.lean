import NMP_Transport_T4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT5 (x : NMP_prepare.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
def fromT5 (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : NMP_prepare.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
@[simp] theorem toT5_inverse (x : NMP_prepare.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromT5 (toT5 x)=x := by
 cases x <;> simp [toT5,fromT5]
#print axioms toT5_inverse
@[simp] theorem fromT5_inverse (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toT5 (fromT5 x)=x := by
 cases x <;> simp [fromT5,toT5]
#print axioms fromT5_inverse
end AspisR1.NMP_Transport
