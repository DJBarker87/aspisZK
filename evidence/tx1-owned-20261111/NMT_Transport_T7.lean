import NMT_Transport_T6
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT7 (x : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def fromT7 (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
@[simp] theorem toT7_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromT7 (toT7 x)=x := by
 cases x <;> simp [toT7,fromT7]
#print axioms toT7_inverse
@[simp] theorem fromT7_inverse (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toT7 (fromT7 x)=x := by
 cases x <;> simp [fromT7,toT7]
#print axioms fromT7_inverse
end AspisR1.NMT_Transport
