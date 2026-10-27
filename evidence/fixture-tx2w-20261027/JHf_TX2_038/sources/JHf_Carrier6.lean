import JHf_Carrier5
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestTerminalStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1WithdrawalPublicV1 (x1))

def fromPoolV1PairForestTerminalStatementV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1WithdrawalPublicV1 (x1))
theorem from_toPoolV1PairForestTerminalStatementV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    fromPoolV1PairForestTerminalStatementV1 (toPoolV1PairForestTerminalStatementV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestTerminalStatementV1
end AspisR1.JHf_Carrier
