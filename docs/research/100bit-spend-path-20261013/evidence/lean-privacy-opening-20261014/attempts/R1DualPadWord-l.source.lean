import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-! A purely linear word-level identity for a dual-pad correction. This module
does not assert that suitable masks exist or establish any protocol privacy. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DualPadWord

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
variable {C I : Type*} [Fintype C]

def embed (w : I → K) : I → E := fun i => algebraMap K E (w i)

def repair (u : C → K) (delta noise : C → I → K) : I → K :=
  fun i => -∑ c, u c * (delta c i - noise c i)

theorem repair_eq (u : C → K) (delta noise : C → I → K) :
    repair u delta noise = -∑ c, u c • (delta c - noise c) := by
  funext i
  simp [repair, Finset.sum_fn]

theorem repair_mem (B : Submodule K (I → K)) (u : C → K)
    (delta noise : C → I → K)
    (hdelta : ∀ c, delta c ∈ B) (hnoise : ∀ c, noise c ∈ B) :
    repair u delta noise ∈ B := by
  rw [repair_eq]
  apply B.neg_mem
  apply Submodule.sum_mem
  intro c hc
  exact B.smul_mem (u c) (B.sub_mem (hdelta c) (hnoise c))

theorem repair_raw_zero {O : Type*} [AddCommGroup O] [Module K O]
    (raw : (I → K) →ₗ[K] O) (u : C → K)
    (delta noise : C → I → K)
    (heq : ∀ c, raw (noise c) = raw (delta c)) :
    raw (repair u delta noise) = 0 := by
  rw [repair_eq]
  simp only [map_neg, map_sum, map_smul, map_sub, heq, sub_self,
    smul_zero, Finset.sum_const_zero]
  simp

theorem full_word_eq (a : C → E) (g d : E) (u v : C → K)
    (delta noise : C → I → K)
    (hcancel : ∀ c, a c + g * algebraMap K E (u c) + d * algebraMap K E (v c) = 0) :
    (fun i => ∑ c, a c * algebraMap K E (noise c i)) +
        g • embed (repair u delta noise) + d • embed (repair v delta noise) =
      fun i => ∑ c, a c * algebraMap K E (delta c i) := by
  funext i
  rw [repair_eq, repair_eq]
  simp only [Pi.add_apply, Pi.smul_apply, embed, smul_eq_mul, Finset.sum_fn]
  simp only [Pi.neg_apply, Pi.sub_apply]
  rw [map_neg, map_sum, map_neg, map_sum]
  simp only [map_mul, map_sub]
  rw [mul_neg, Finset.mul_sum, mul_neg, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have h := hcancel c
  linear_combination (algebraMap K E (noise c i - delta c i)) * h

theorem correction {B : Submodule K (I → K)} {O : Type*}
    [AddCommGroup O] [Module K O]
    (raw : (I → K) →ₗ[K] O) (a : C → E) (g d : E) (u v : C → K)
    (delta noise : C → I → K)
    (hdelta : ∀ c, delta c ∈ B) (hnoise : ∀ c, noise c ∈ B)
    (heq : ∀ c, raw (noise c) = raw (delta c))
    (hcancel : ∀ c, a c + g * algebraMap K E (u c) + d * algebraMap K E (v c) = 0) :
    repair u delta noise ∈ B ∧ repair v delta noise ∈ B ∧
      raw (repair u delta noise) = 0 ∧ raw (repair v delta noise) = 0 ∧
      (fun i => ∑ c, a c * algebraMap K E (noise c i)) +
          g • embed (repair u delta noise) + d • embed (repair v delta noise) =
        fun i => ∑ c, a c * algebraMap K E (delta c i) := by
  exact ⟨repair_mem B u delta noise hdelta hnoise,
    repair_mem B v delta noise hdelta hnoise,
    repair_raw_zero raw u delta noise heq,
    repair_raw_zero raw v delta noise heq,
    full_word_eq a g d u v delta noise hcancel⟩

#print axioms repair_mem
#print axioms repair_eq
#print axioms repair_raw_zero
#print axioms full_word_eq
#print axioms correction

end AspisR1.DualPadWord
end
