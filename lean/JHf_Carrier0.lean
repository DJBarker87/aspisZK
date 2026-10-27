import AdapterRwModel
import AspisR1AdapterReconstruct.Funs
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairLiveSnapshotV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

def fromPoolV1PairLiveSnapshotV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}
theorem from_toPoolV1PairLiveSnapshotV1 (v : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    fromPoolV1PairLiveSnapshotV1 (toPoolV1PairLiveSnapshotV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1]
  all_goals rfl
#print axioms from_toPoolV1PairLiveSnapshotV1
end AspisR1.JHf_Carrier
