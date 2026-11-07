import NMT_Transport_T5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT6 (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def fromT6 (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
@[simp] theorem toT6_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromT6 (toT6 x)=x := by
 cases x <;> simp [toT6,fromT6]
#print axioms toT6_inverse
@[simp] theorem fromT6_inverse (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toT6 (fromT6 x)=x := by
 cases x <;> simp [fromT6,toT6]
#print axioms fromT6_inverse
end AspisR1.NMT_Transport
