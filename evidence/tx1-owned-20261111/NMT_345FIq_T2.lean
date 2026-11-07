import NMT_345FIq_T1
import NKR_DigestChildren
import NKR_TermPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345FIq
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT2 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def fromT2 (x : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
@[simp] theorem toT2_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromT2 (toT2 x) = x := by
 cases x <;> simp [toT2,fromT2]
#print axioms toT2_inverse
@[simp] theorem fromT2_inverse (x : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toT2 (fromT2 x) = x := by
 cases x <;> simp [fromT2,toT2]
#print axioms fromT2_inverse
end NMT_345FIq
