import JHf_Carrier3
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PrivateTransferPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

def fromPoolV1PrivateTransferPublicV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}
theorem from_toPoolV1PrivateTransferPublicV1 (v : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    fromPoolV1PrivateTransferPublicV1 (toPoolV1PrivateTransferPublicV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1]
  all_goals rfl
#print axioms from_toPoolV1PrivateTransferPublicV1
end AspisR1.JHf_Carrier
