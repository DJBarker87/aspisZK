import NMT_345First_T3
import NMT_first.Types
set_option autoImplicit false
noncomputable section
namespace NMT_345First
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT4 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NMT_first.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨toT2 (x.live_snapshot),toT3 (x.candidate_afterstate)⟩
def fromT4 (x : NMT_first.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨fromT2 (x.live_snapshot),fromT3 (x.candidate_afterstate)⟩
@[simp] theorem toT4_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromT4 (toT4 x) = x := by
 cases x <;> simp [toT4,fromT4]
#print axioms toT4_inverse
@[simp] theorem fromT4_inverse (x : NMT_first.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toT4 (fromT4 x) = x := by
 cases x <;> simp [fromT4,toT4]
#print axioms fromT4_inverse
end NMT_345First
