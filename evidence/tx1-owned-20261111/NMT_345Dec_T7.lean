import NMT_345Dec_T6
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT7 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
 ⟨x.master_account,x.checkpoint_account,x.selected_lane_account,x.output_lane,x.checkpoint_sequence,x.historical_global_anchor,toT6 (x.lane_transition)⟩
def fromT7 (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
 ⟨x.master_account,x.checkpoint_account,x.selected_lane_account,x.output_lane,x.checkpoint_sequence,x.historical_global_anchor,fromT6 (x.lane_transition)⟩
@[simp] theorem toT7_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : fromT7 (toT7 x) = x := by
 cases x <;> simp [toT7,fromT7]
#print axioms toT7_inverse
@[simp] theorem fromT7_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : toT7 (fromT7 x) = x := by
 cases x <;> simp [fromT7,toT7]
#print axioms fromT7_inverse
end NMT_345Dec
