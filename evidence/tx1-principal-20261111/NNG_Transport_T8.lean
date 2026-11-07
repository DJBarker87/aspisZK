import NNG_Transport_T7
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT8 (x : NNG_verify_finish.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨toT6 (x.live_snapshot),toT7 (x.candidate_afterstate)⟩
def fromT8 (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NNG_verify_finish.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨fromT6 (x.live_snapshot),fromT7 (x.candidate_afterstate)⟩
@[simp] theorem toT8_inverse (x : NNG_verify_finish.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromT8 (toT8 x)=x := by
 cases x <;> simp [toT8,fromT8]
#print axioms toT8_inverse
@[simp] theorem fromT8_inverse (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toT8 (fromT8 x)=x := by
 cases x <;> simp [fromT8,toT8]
#print axioms fromT8_inverse
end AspisR1.NNG_Transport
