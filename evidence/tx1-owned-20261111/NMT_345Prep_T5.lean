import NMT_345Prep_T4
import NJB_SemanticPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345Prep
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT5 : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (toT1 (x0)) (toT4 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (toT0 (x0)) (toT4 (x1))
def fromT5 : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public → NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (fromT1 (x0)) (fromT4 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (fromT0 (x0)) (fromT4 (x1))
@[simp] theorem toT5_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : fromT5 (toT5 x) = x := by
 cases x <;> simp [toT5,fromT5]
#print axioms toT5_inverse
@[simp] theorem fromT5_inverse (x : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) : toT5 (fromT5 x) = x := by
 cases x <;> simp [fromT5,toT5]
#print axioms fromT5_inverse
end NMT_345Prep
