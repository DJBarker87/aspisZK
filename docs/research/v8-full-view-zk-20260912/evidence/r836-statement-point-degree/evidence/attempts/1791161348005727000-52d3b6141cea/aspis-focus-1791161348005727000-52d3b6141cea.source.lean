import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import AspisV8R19.R745JointObservationPolynomial
import AspisV8R19.SourceStatementPoints
import AspisV8R17.SourceOriginalWeights

/-! Degree bounds for the exact ten-coordinate source statement points. -/
set_option autoImplicit false
namespace AspisV8R19.R836StatementPointDegree
open MvPolynomial
open AspisV8R17 AspisR19
open AspisR19.SourceStatementPoints
open AspisV8R19.R745JointObservationPolynomial
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F]

lemma pZ_degree (i : Fin 10) :
    (pZ (F := F) i).totalDegree ≤ 1 := by
  unfold pZ
  simp

lemma carry_degree (i : Fin 10) :
    (ResidualModel.carry (pZ (F := F)) i).totalDegree ≤ 9 - i.val := by
  unfold ResidualModel.carry
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k : Fin 10, if i.val < k.val then 1 else 0 := by
      apply Finset.sum_le_sum
      intro k _
      split
      · exact pZ_degree k
      · simp
    _ = 9 - i.val := by
      fin_cases i <;> norm_num [Fin.sum_univ_succ]

theorem statement_point_degree (p : Fin 3) (i : Fin 10) :
    (SourceStatementPoints.points (pZ (F := F)) p i).totalDegree ≤ 10 - i.val := by
  rw [SourceStatementPoints.points_eq]
  fin_cases p
  · simpa using pZ_degree i
  · simp only [ResidualModel.point, ↓reduceIte, ↓reduceDIte]
    have hz := pZ_degree (F := F) i
    have hc := carry_degree (F := F) i
    have hmul : ((2 : JointPoly F) * pZ i *
        ResidualModel.carry (pZ (F := F)) i).totalDegree ≤ 10 - i.val := by
      have h2 : ((2 : JointPoly F)).totalDegree ≤ 0 := by simp
      exact (totalDegree_mul _ _).trans
        (Nat.add_le_add ((totalDegree_mul _ _).trans (Nat.add_le_add h2 hz)) hc) |>.trans (by omega)
    exact (totalDegree_sub _ _).trans
      (max_le ((totalDegree_add _ _).trans (max_le hz hc)) hmul) |>.trans (by omega)
  · simp only [ResidualModel.point, ↓reduceIte, ↓reduceDIte]
    split
    · exact (totalDegree_sub _ _).trans (max_le (by simp) (pZ_degree i)) |>.trans (by omega)
    · exact (pZ_degree i).trans (by omega)

theorem source_point_basis_degree (p : Fin 3) (n : Nat) :
    (sourcePointBasis (SourceStatementPoints.points (pZ (F := F)) p) n).totalDegree ≤ 55 := by
  unfold sourcePointBasis sourceMultilinearFactors
  simp only [List.prod_ofFn]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i : Fin 10, (10 - i.val) := by
      apply Finset.sum_le_sum
      intro i _
      split
      · exact (totalDegree_sub _ _).trans
          (max_le (by simp) (statement_point_degree (F := F) p i))
      · exact statement_point_degree (F := F) p i
    _ = 55 := by norm_num [Fin.sum_univ_succ]

#print axioms pZ_degree
#print axioms carry_degree
#print axioms statement_point_degree
#print axioms source_point_basis_degree
end
end AspisV8R19.R836StatementPointDegree
