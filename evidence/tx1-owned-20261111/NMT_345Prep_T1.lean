import NMT_345Prep_T0
import NJB_SemanticPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345Prep
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT1 (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
def fromT1 (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
@[simp] theorem toT1_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromT1 (toT1 x) = x := by
 cases x <;> simp [toT1,fromT1]
#print axioms toT1_inverse
@[simp] theorem fromT1_inverse (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toT1 (fromT1 x) = x := by
 cases x <;> simp [fromT1,toT1]
#print axioms fromT1_inverse
end NMT_345Prep
