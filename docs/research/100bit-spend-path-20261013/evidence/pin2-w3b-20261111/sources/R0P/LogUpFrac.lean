import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace R0P

open Polynomial

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- Common numerator for the signed partial-fraction sum on `D`. -/
def numer (D : Finset K) (m : K → K) : K[X] := by
  classical
  exact ∑ v ∈ D, C (m v) * ∏ u ∈ D.erase v, (X - C u)

private theorem numer_eval (D : Finset K) (m : K → K) (x : K) :
    (numer D m).eval x =
      ∑ v ∈ D, m v * ∏ u ∈ D.erase v, (x - u) := by
  classical
  simp [numer, Polynomial.eval_finsetSum, Polynomial.eval_prod]

#print axioms numer_eval

private theorem numer_eval_mem (D : Finset K) (m : K → K)
    (v : K) (hv : v ∈ D) :
    (numer D m).eval v = m v * ∏ u ∈ D.erase v, (v - u) := by
  classical
  rw [numer_eval]
  rw [Finset.sum_eq_single_of_mem v hv (by
    intro w hw hne
    have hvw : v ∈ D.erase w := Finset.mem_erase.mpr ⟨Ne.symm hne, hv⟩
    have hz : (∏ u ∈ D.erase w, (v - u)) = 0 :=
      Finset.prod_eq_zero hvw (sub_self v)
    rw [hz]
    exact mul_zero _)]

#print axioms numer_eval_mem

/-- Vanishing numerator forces every signed coefficient on its support to
vanish; evaluation at each member isolates that coefficient. -/
theorem numer_eq_zero_imp (D : Finset K) (m : K → K)
    (h : numer D m = 0) : ∀ v ∈ D, m v = 0 := by
  classical
  intro v hv
  have he := congrArg (fun p : K[X] => p.eval v) h
  rw [numer_eval_mem D m v hv, Polynomial.eval_zero] at he
  have hp : (∏ u ∈ D.erase v, (v - u)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun u hu =>
      sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hu).1)
  exact (mul_eq_zero.mp he).resolve_right hp

#print axioms numer_eq_zero_imp

private theorem numer_term_natDegree_le (D : Finset K) (m : K → K)
    (v : K) (hv : v ∈ D) :
    (C (m v) * ∏ u ∈ D.erase v, (X - C u)).natDegree ≤ D.card - 1 := by
  classical
  have hprod : (∏ u ∈ D.erase v, (X - C u)).natDegree ≤ (D.erase v).card := by
    calc
      _ ≤ ∑ u ∈ D.erase v, (X - C u).natDegree :=
        Polynomial.natDegree_prod_le (D.erase v) (fun u => X - C u)
      _ = (D.erase v).card := by simp
  calc
    _ ≤ natDegree (C (m v)) + (∏ u ∈ D.erase v, (X - C u)).natDegree :=
      natDegree_mul_le
    _ ≤ 0 + (D.erase v).card := by
      exact Nat.add_le_add (by simp) hprod
    _ = D.card - 1 := by simp [Finset.card_erase_of_mem hv]

#print axioms numer_term_natDegree_le

/-- The numerator degree is bounded by one less than the number of distinct
support values, with no nonzero or splitting assumption. -/
private theorem numer_natDegree_le (D : Finset K) (m : K → K) :
    (numer D m).natDegree ≤ D.card - 1 := by
  classical
  apply natDegree_sum_le_of_forall_le (s := D)
  intro v hv
  exact numer_term_natDegree_le D m v hv

#print axioms numer_natDegree_le

/-- The multiplicity-counted roots of a nonzero numerator obey the same
support-size bound. -/
theorem numer_nonzero_bounds (D : Finset K) (m : K → K)
    (h : numer D m ≠ 0) : (numer D m).natDegree ≤ D.card - 1 ∧
      (numer D m).roots.card ≤ D.card - 1 := by
  by_cases hz : numer D m = 0
  · exact (h hz).elim
  · constructor
    · exact numer_natDegree_le D m
    · calc
        _ ≤ (numer D m).natDegree := Polynomial.card_roots' (numer D m)
        _ ≤ D.card - 1 := numer_natDegree_le D m

#print axioms numer_nonzero_bounds

private theorem numer_frac_mul_den (D : Finset K) (m : K → K)
    (chi : K) (hchi : chi ∉ D) :
    (∑ v ∈ D, m v / (chi - v)) * (∏ u ∈ D, (chi - u)) =
      (numer D m).eval chi := by
  classical
  rw [Finset.sum_mul, numer_eval]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.prod_erase_mul D (fun u => chi - u) hv]
  have hpole : chi - v ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hchi (h ▸ hv)
  field_simp [hpole]

#print axioms numer_frac_mul_den

/-- Literal partial-fraction identity away from the distinct support values. -/
theorem numer_partial_fraction (D : Finset K) (m : K → K)
    (chi : K) (hchi : chi ∉ D) :
    ∑ v ∈ D, m v / (chi - v) =
      (numer D m).eval chi / ∏ u ∈ D, (chi - u) := by
  classical
  apply (eq_div_iff ?_).2
  · exact numer_frac_mul_den D m chi hchi
  · exact Finset.prod_ne_zero_iff.mpr fun u hu => by
      apply sub_ne_zero.mpr
      intro h
      exact hchi (h ▸ hu)

#print axioms numer_partial_fraction

end R0P

end
