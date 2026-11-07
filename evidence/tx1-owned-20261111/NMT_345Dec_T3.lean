import NMT_345Dec_T2
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT3 (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
def fromT3 (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
@[simp] theorem toT3_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromT3 (toT3 x) = x := by
 cases x <;> simp [toT3,fromT3]
#print axioms toT3_inverse
@[simp] theorem fromT3_inverse (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toT3 (fromT3 x) = x := by
 cases x <;> simp [fromT3,toT3]
#print axioms fromT3_inverse
end NMT_345Dec
