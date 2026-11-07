import NMT_345Dec_T5
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT6 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨toT4 (x.live_snapshot),toT5 (x.candidate_afterstate)⟩
def fromT6 (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨fromT4 (x.live_snapshot),fromT5 (x.candidate_afterstate)⟩
@[simp] theorem toT6_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromT6 (toT6 x) = x := by
 cases x <;> simp [toT6,fromT6]
#print axioms toT6_inverse
@[simp] theorem fromT6_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toT6 (fromT6 x) = x := by
 cases x <;> simp [fromT6,toT6]
#print axioms fromT6_inverse
end NMT_345Dec
