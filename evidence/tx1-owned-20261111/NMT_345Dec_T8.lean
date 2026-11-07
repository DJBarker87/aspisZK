import NMT_345Dec_T7
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT8 : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
 | .PrivateTransfer x0 x1 => .PrivateTransfer (toT7 (x0)) (toT3 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (toT7 (x0)) (toT2 (x1))
def fromT8 : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
 | .PrivateTransfer x0 x1 => .PrivateTransfer (fromT7 (x0)) (fromT3 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (fromT7 (x0)) (fromT2 (x1))
@[simp] theorem toT8_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : fromT8 (toT8 x) = x := by
 cases x <;> simp [toT8,fromT8]
#print axioms toT8_inverse
@[simp] theorem fromT8_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : toT8 (fromT8 x) = x := by
 cases x <;> simp [fromT8,toT8]
#print axioms fromT8_inverse
end NMT_345Dec
