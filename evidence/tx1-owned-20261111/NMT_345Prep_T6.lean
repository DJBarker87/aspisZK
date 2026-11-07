import NMT_345Prep_T5
import NJB_SemanticPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345Prep
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT6 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
 ⟨x.master_account,x.checkpoint_account,x.selected_lane_account,x.output_lane,x.checkpoint_sequence,x.historical_global_anchor,toT4 (x.lane_transition)⟩
def fromT6 (x : AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
 ⟨x.master_account,x.checkpoint_account,x.selected_lane_account,x.output_lane,x.checkpoint_sequence,x.historical_global_anchor,fromT4 (x.lane_transition)⟩
@[simp] theorem toT6_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : fromT6 (toT6 x) = x := by
 cases x <;> simp [toT6,fromT6]
#print axioms toT6_inverse
@[simp] theorem fromT6_inverse (x : AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : toT6 (fromT6 x) = x := by
 cases x <;> simp [fromT6,toT6]
#print axioms fromT6_inverse
end NMT_345Prep
