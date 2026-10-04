import AspisV8R19.R708ClearedCircleSubstitution
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R712ClearedCircleEvaluation
open scoped BigOperators
open Polynomial
open AspisV8R19.R708ClearedCircleSubstitution

variable {F : Type*} [Field F]

lemma base_eval_circle (u : F) (hu : u ≠ 0) :
    (base (F:=F)).eval u = u * (-(u + u⁻¹)) := by
  unfold base
  rw [eval_neg, eval_add, eval_pow, eval_X, eval_C]
  field_simp

lemma cleared_eval_circle (P : Polynomial F) (u : F) (hu : u ≠ 0) :
    (cleared P).eval u = u ^ P.natDegree * P.eval (-(u + u⁻¹)) := by
  unfold cleared
  rw [eval_finsetSum, eval_eq_sum_range, Finset.mul_sum]
  simp_rw [eval_mul, eval_C, eval_pow, eval_X, base_eval_circle u hu]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [mul_pow]
  have hpow : u^n * u^(P.natDegree-n) = u^P.natDegree := by
    rw [← pow_add]
    congr 1
    omega
  calc
    P.coeff n * ((u^n * (-(u + u⁻¹))^n) * u^(P.natDegree-n)) =
        (u^n * u^(P.natDegree-n)) * (P.coeff n * (-(u + u⁻¹))^n) := by ring
    _ = _ := by rw [hpow]


lemma cleared_natDegree_le (P : Polynomial F) :
    (cleared P).natDegree ≤ 2 * P.natDegree := by
  unfold cleared
  apply natDegree_sum_le_of_forall_le
  intro n hn
  have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  calc
    (C (P.coeff n) * (base (F:=F)^n * X^(P.natDegree-n))).natDegree ≤
        (base (F:=F)^n * X^(P.natDegree-n)).natDegree := natDegree_C_mul_le _ _
    _ ≤ (base (F:=F)^n).natDegree + (X^(P.natDegree-n) : Polynomial F).natDegree := natDegree_mul_le
    _ ≤ n * (base (F:=F)).natDegree + (P.natDegree-n) := by
      gcongr
      · exact natDegree_pow_le (p:=base (F:=F)) (n:=n)
      · simp
    _ ≤ n * 2 + (P.natDegree-n) := by rw [base_natDegree]
    _ ≤ 2 * P.natDegree := by omega

#print axioms base_eval_circle
#print axioms cleared_eval_circle
end AspisV8R19.R712ClearedCircleEvaluation
