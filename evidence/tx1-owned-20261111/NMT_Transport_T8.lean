import NMT_Transport_T7
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT8 (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨toT6 (x.live_snapshot),toT7 (x.candidate_afterstate)⟩
def fromT8 (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨fromT6 (x.live_snapshot),fromT7 (x.candidate_afterstate)⟩
@[simp] theorem toT8_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromT8 (toT8 x)=x := by
 cases x <;> simp [toT8,fromT8]
#print axioms toT8_inverse
@[simp] theorem fromT8_inverse (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toT8 (fromT8 x)=x := by
 cases x <;> simp [fromT8,toT8]
#print axioms fromT8_inverse
end AspisR1.NMT_Transport
