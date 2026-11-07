import NMP_Transport_T8
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT9 : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (toT5 (x0)) (toT8 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (toT4 (x0)) (toT8 (x1))
def fromT9 : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public → NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (fromT5 (x0)) (fromT8 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (fromT4 (x0)) (fromT8 (x1))
@[simp] theorem toT9_inverse (x : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : fromT9 (toT9 x)=x := by
 cases x <;> simp [toT9,fromT9]
#print axioms toT9_inverse
@[simp] theorem fromT9_inverse (x : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) : toT9 (fromT9 x)=x := by
 cases x <;> simp [fromT9,toT9]
#print axioms fromT9_inverse
end AspisR1.NMP_Transport
