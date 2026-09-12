/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.AdaptiveHazard
noncomputable section
variable {S A : Type*} [Fintype A]

/-- State may include the entire adversary/RO prefix. Thus no independence
between successive states is assumed. Freshness and the per-state bound
must be derived for the actual source before applying the theorem. -/
structure Kernel (S A : Type*) [Fintype A] where
  weight : S → A → ℚ
  nonneg : ∀ s a, 0 ≤ weight s a
  total : ∀ s, (∑ a, weight s a) = 1
  next : S → A → S
  hit : S → A → Bool

def localMass (k : Kernel S A) (s : S) : ℚ :=
  ∑ a, k.weight s a * if k.hit s a then 1 else 0

def ever (k : Kernel S A) : Nat → S → ℚ
  | 0, _ => 0
  | n+1, s => ∑ a, k.weight s a *
      (if k.hit s a then 1 else ever k n (k.next s a))

theorem ever_nonneg (k : Kernel S A) : ∀ n s, 0 ≤ ever k n s := by
  intro n
  induction n with
  | zero => intro s; simp [ever]
  | succ n ih =>
    intro s
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (k.nonneg s a)
    split_ifs
    · norm_num
    · exact ih _

theorem ever_le_one (k : Kernel S A) : ∀ n s, ever k n s ≤ 1 := by
  intro n
  induction n with
  | zero => intro s; norm_num [ever]
  | succ n ih =>
    intro s
    calc
      ever k (n+1) s ≤ ∑ a, k.weight s a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (k.nonneg s a)
        split_ifs
        · exact le_rfl
        · exact ih _
      _ = 1 := by simp only [mul_one]; exact k.total s

/-- Adaptive union bound derived by recursion, not supplied as a field. -/
theorem ever_le_budget (k : Kernel S A) (ε : ℚ) (εnonneg : 0 ≤ ε)
    (stepBound : ∀ s, localMass k s ≤ ε) :
    ∀ n s, ever k n s ≤ (n : ℚ)*ε := by
  intro n
  induction n with
  | zero => intro s; simp [ever]
  | succ n ih =>
    intro s
    have budgetNonneg : 0 ≤ (n : ℚ)*ε := mul_nonneg (Nat.cast_nonneg n) εnonneg
    calc
      ever k (n+1) s ≤ ∑ a, k.weight s a *
          ((if k.hit s a then (1:ℚ) else 0)+(n:ℚ)*ε) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (k.nonneg s a)
        by_cases hit : k.hit s a = true
        · simp only [hit, Bool.true_eq, ↓reduceIte]
          linarith
        · have no : k.hit s a = false := Bool.eq_false_iff.mpr hit
          simp only [no, Bool.false_eq_true, ↓reduceIte, zero_add]
          exact ih _
      _ = localMass k s + (n:ℚ)*ε := by
        simp only [mul_add, Finset.sum_add_distrib, localMass]
        rw [← Finset.sum_mul, k.total, one_mul]
      _ ≤ ε+(n:ℚ)*ε := add_le_add_right (stepBound s) _
      _ = ((n+1:Nat):ℚ)*ε := by push_cast; ring

#print axioms ever_le_budget
end
end AspisV8Completion.AdaptiveHazard
