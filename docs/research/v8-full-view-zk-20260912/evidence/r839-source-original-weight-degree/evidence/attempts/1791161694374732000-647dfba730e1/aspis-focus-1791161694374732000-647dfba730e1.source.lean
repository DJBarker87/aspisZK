import Mathlib.Algebra.MvPolynomial.CommRing
import AspisV8R19.R836StatementPointDegree
import AspisV8R17.SourceOriginalWeights

/-! Degree bound for the ordinary branch of the exact source original weight. -/
set_option autoImplicit false
namespace AspisV8R19.R839SourceOriginalWeightDegree
open MvPolynomial
open AspisV8R17 AspisR19
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R836StatementPointDegree
noncomputable section

variable {F : Type*} [Field F]

lemma pKappa_degree :
    (pKappa (F := F)).totalDegree ≤ 1 := by
  unfold pKappa
  simp

lemma pKappa_pow_degree (e : Nat) :
    ((pKappa (F := F)) ^ e).totalDegree ≤ e := by
  exact (totalDegree_pow _ _).trans (by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left e (pKappa_degree (F := F)))

theorem ordinary_sourceOriginalWeight_degree
    (inactive : Finset (Fin 1024)) (g : Fin 1024 → JointPoly F) (i : Fin 1024) :
    (sourceOriginalWeight (SourceStatementPoints.points (pZ (F := F)))
      (pKappa (F := F)) inactive g false i).totalDegree ≤ 58 := by
  rw [sourceOriginalWeight_eq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hb (p : Fin 3) :
      (sourcePointBasis (SourceStatementPoints.points (pZ (F := F)) p) i.val).totalDegree ≤ 55 :=
    source_point_basis_degree (F := F) p i.val
  have h1 :
      ((pKappa (F := F)) * sourcePointBasis
        (SourceStatementPoints.points (pZ (F := F)) 0) i.val).totalDegree ≤ 58 := by
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (pKappa_degree (F := F)) (hb 0)) |>.trans (by omega)
  have h2 :
      ((pKappa (F := F)) ^ 2 * sourcePointBasis
        (SourceStatementPoints.points (pZ (F := F)) 1) i.val).totalDegree ≤ 58 := by
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (pKappa_pow_degree (F := F) 2) (hb 1)) |>.trans (by omega)
  have h3 :
      ((pKappa (F := F)) ^ 3 * sourcePointBasis
        (SourceStatementPoints.points (pZ (F := F)) 2) i.val).totalDegree ≤ 58 := by
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (pKappa_pow_degree (F := F) 3) (hb 2))
  have hi : ((if i ∈ inactive then (1 : JointPoly F) else 0)).totalDegree ≤ 58 := by
    split <;> simp
  exact (totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le h1 h2)) h3)) hi)

#print axioms pKappa_degree
#print axioms pKappa_pow_degree
#print axioms ordinary_sourceOriginalWeight_degree
end
end AspisV8R19.R839SourceOriginalWeightDegree
