import AspisV8R19.R374SingleCoordinateDegree
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false
namespace AspisV8R19.R377SelectorCoordinateDegree
open Polynomial
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

abbrev Coord := Fin 10

/-- The selector factor product used by the source's low/high coordinate tables. -/
def selectorPolynomial (coords : Finset Coord) (bits : Coord → Bool)
    (z : Coord → F) (j : Coord) : F[X] :=
  ∏ k ∈ coords, if bits k then AspisR19.R374SingleCoordinateDegree.line z j k
    else 1 - AspisR19.R374SingleCoordinateDegree.line z j k

theorem selectorPolynomial_degree (coords : Finset Coord) (bits : Coord → Bool)
    (z : Coord → F) (j : Coord) :
    (selectorPolynomial coords bits z j).natDegree ≤ if j ∈ coords then 1 else 0 := by
  rw [selectorPolynomial]
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ k ∈ coords, (if k = j then 1 else 0 : Nat) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hb : bits k
      · simp only [if_pos hb]
        exact AspisR19.R374SingleCoordinateDegree.line_degree z j k
      · simp only [if_neg hb]
        exact AspisR19.R374SingleCoordinateDegree.sub_bound (by simp)
          (AspisR19.R374SingleCoordinateDegree.line_degree z j k)
    _ = if j ∈ coords then 1 else 0 := by
      simp [Finset.sum_ite_irrel]

theorem selectorPolynomial_eval (coords : Finset Coord) (bits : Coord → Bool)
    (z : Coord → F) (j : Coord) (x : F) :
    (selectorPolynomial coords bits z j).eval x =
      ∏ k ∈ coords, if bits k then Function.update z j x k
        else 1 - Function.update z j x k := by
  rw [selectorPolynomial, eval_prod]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hb : bits k
  · simp only [if_pos hb, eval_prod]
    exact AspisR19.R374SingleCoordinateDegree.line_eval z j k x
  · simp only [if_neg hb, eval_sub, eval_one]
    rw [AspisR19.R374SingleCoordinateDegree.line_eval]

/-- A finite weighted family of coordinate selector products. -/
def weightedSelectorPolynomial {n : Nat} (coeff : Fin n → F)
    (bits : Fin n → Coord → Bool) (coords : Finset Coord)
    (z : Coord → F) (j : Coord) : F[X] :=
  ∑ r : Fin n, Polynomial.C (coeff r) * selectorPolynomial coords (bits r) z j

theorem weightedSelectorPolynomial_degree {n : Nat} (coeff : Fin n → F)
    (bits : Fin n → Coord → Bool) (coords : Finset Coord)
    (z : Coord → F) (j : Coord) :
    (weightedSelectorPolynomial coeff bits coords z j).natDegree ≤
      if j ∈ coords then 1 else 0 := by
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hs := selectorPolynomial_degree coords (bits r) z j
  calc
    _ ≤ (Polynomial.C (coeff r)).natDegree +
        (selectorPolynomial coords (bits r) z j).natDegree := natDegree_mul_le
    _ ≤ if j ∈ coords then 1 else 0 := by simpa using hs

theorem weightedSelectorPolynomial_eval {n : Nat} (coeff : Fin n → F)
    (bits : Fin n → Coord → Bool) (coords : Finset Coord)
    (z : Coord → F) (j : Coord) (x : F) :
    (weightedSelectorPolynomial coeff bits coords z j).eval x =
      ∑ r : Fin n, coeff r *
        (∏ k ∈ coords, if bits r k then Function.update z j x k
          else 1 - Function.update z j x k) := by
  unfold weightedSelectorPolynomial
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [eval_mul, eval_C, selectorPolynomial_eval]

#print axioms selectorPolynomial_degree
#print axioms selectorPolynomial_eval
#print axioms weightedSelectorPolynomial_degree
#print axioms weightedSelectorPolynomial_eval
end
end AspisV8R19.R377SelectorCoordinateDegree
