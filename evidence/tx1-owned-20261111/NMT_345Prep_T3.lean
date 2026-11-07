import NMT_345Prep_T2
import NJB_SemanticPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345Prep
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT3 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def fromT3 (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
@[simp] theorem toT3_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromT3 (toT3 x) = x := by
 cases x <;> simp [toT3,fromT3]
#print axioms toT3_inverse
@[simp] theorem fromT3_inverse (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toT3 (fromT3 x) = x := by
 cases x <;> simp [fromT3,toT3]
#print axioms fromT3_inverse
end NMT_345Prep
