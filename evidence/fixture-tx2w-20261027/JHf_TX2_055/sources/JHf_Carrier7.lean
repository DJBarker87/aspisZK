import JHf_Carrier6
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolIdentityV1 (value : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.PoolIdentityV1 :=
  {pool:=value.pool,asset_mint:=value.asset_mint,token_program:=value.token_program,asset_id:=value.asset_id,deployment_domain:=value.deployment_domain}
def fromPoolIdentityV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.PoolIdentityV1) : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1 :=
  {pool:=value.pool,asset_mint:=value.asset_mint,token_program:=value.token_program,asset_id:=value.asset_id,deployment_domain:=value.deployment_domain}
theorem from_toPoolIdentityV1 (v : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : fromPoolIdentityV1 (toPoolIdentityV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1]
  all_goals rfl
#print axioms from_toPoolIdentityV1
end AspisR1.JHf_Carrier
