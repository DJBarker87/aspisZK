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


lemma exists_circle_eval_ne_zero [Fintype F] (P : Polynomial F)
    (hcard : 2 * P.natDegree + 1 < Fintype.card F) (hP : P ≠ 0) :
    ∃ u : F, u ≠ 0 ∧ P.eval (-(u + u⁻¹)) ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ u : F, (X * cleared P).eval u = 0 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · rw [eval_mul, cleared_eval_circle P u hu, h u hu]
      simp
  have hdeg : (X * cleared P).natDegree < Fintype.card F := by
    calc
      (X * cleared P).natDegree ≤ X.natDegree + (cleared P).natDegree := natDegree_mul_le
      _ ≤ 1 + 2 * P.natDegree := by simp [cleared_natDegree_le]
      _ < Fintype.card F := by omega
  have hz : X * cleared P = 0 :=
    eq_of_natDegree_lt_card_of_eval_eq (X * cleared P) 0 Function.injective_id
      (fun u => by simpa using hall u) (by simpa using hdeg)
  exact mul_ne_zero X_ne_zero (cleared_ne_zero P hP) hz

#print axioms base_eval_circle
#print axioms cleared_natDegree_le
#print axioms exists_circle_eval_ne_zero
#print axioms cleared_eval_circle
end AspisV8R19.R712ClearedCircleEvaluation
