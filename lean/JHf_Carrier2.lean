import JHf_Carrier1
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairLatePublicStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=toPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

def fromPoolV1PairLatePublicStatementV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=fromPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}
theorem from_toPoolV1PairLatePublicStatementV1 (v : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    fromPoolV1PairLatePublicStatementV1 (toPoolV1PairLatePublicStatementV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1]
  all_goals rfl
#print axioms from_toPoolV1PairLatePublicStatementV1
end AspisR1.JHf_Carrier
