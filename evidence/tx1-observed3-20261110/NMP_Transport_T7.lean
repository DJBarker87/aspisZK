import NMP_Transport_T6
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT7 (x : NMP_prepare.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def fromT7 (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NMP_prepare.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
@[simp] theorem toT7_inverse (x : NMP_prepare.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromT7 (toT7 x)=x := by
 cases x <;> simp [toT7,fromT7]
#print axioms toT7_inverse
@[simp] theorem fromT7_inverse (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toT7 (fromT7 x)=x := by
 cases x <;> simp [fromT7,toT7]
#print axioms fromT7_inverse
end AspisR1.NMP_Transport
