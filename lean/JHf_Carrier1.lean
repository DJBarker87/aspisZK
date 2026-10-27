import JHf_Carrier0
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairVerifiedAfterstateV1 (value : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

def fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}
theorem from_toPoolV1PairVerifiedAfterstateV1 (v : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    fromPoolV1PairVerifiedAfterstateV1 (toPoolV1PairVerifiedAfterstateV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1]
  all_goals rfl
#print axioms from_toPoolV1PairVerifiedAfterstateV1
end AspisR1.JHf_Carrier
