import NMT_345Dec_T3
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT4 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def fromT4 (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
@[simp] theorem toT4_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromT4 (toT4 x) = x := by
 cases x <;> simp [toT4,fromT4]
#print axioms toT4_inverse
@[simp] theorem fromT4_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toT4 (fromT4 x) = x := by
 cases x <;> simp [fromT4,toT4]
#print axioms fromT4_inverse
end NMT_345Dec
