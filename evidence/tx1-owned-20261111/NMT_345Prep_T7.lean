import NMT_345Prep_T6
import NJB_SemanticPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345Prep
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT7 : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
 | .PrivateTransfer x0 x1 => .PrivateTransfer (toT6 (x0)) (toT1 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (toT6 (x0)) (toT0 (x1))
def fromT7 : AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
 | .PrivateTransfer x0 x1 => .PrivateTransfer (fromT6 (x0)) (fromT1 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (fromT6 (x0)) (fromT0 (x1))
@[simp] theorem toT7_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : fromT7 (toT7 x) = x := by
 cases x <;> simp [toT7,fromT7]
#print axioms toT7_inverse
@[simp] theorem fromT7_inverse (x : AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : toT7 (fromT7 x) = x := by
 cases x <;> simp [fromT7,toT7]
#print axioms fromT7_inverse
end NMT_345Prep
