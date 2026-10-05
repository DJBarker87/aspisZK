import AspisV8R19.R652ResidualCoefficientCompletion
import Mathlib.Tactic

/-! Completion for the actual five retained joint relation indices.
The fourth-root degeneracy remains explicit; alpha zero is allowed. -/
set_option autoImplicit false
namespace AspisV8R19.R853JointCoefficientCompletion
open R652ResidualCoefficientCompletion
open scoped BigOperators
variable {F : Type*} [Field F]

theorem joint_completion (d : Fin 7 → F) (alpha : F)
    (ha : alpha^4 ≠ 1) (he : evalSeven d alpha = 0)
    (hb : d 0 + d 4 = 0)
    (hs : ∀ i : Fin 7, i ≠ 0 → i ≠ 4 → d i = 0) :
    ∀ i, d i = 0 := by
  have h1 : d 1 = 0 := hs 1 (by decide) (by decide)
  have h2 : d 2 = 0 := hs 2 (by decide) (by decide)
  have h3 : d 3 = 0 := hs 3 (by decide) (by decide)
  have h5 : d 5 = 0 := hs 5 (by decide) (by decide)
  have h6 : d 6 = 0 := hs 6 (by decide) (by decide)
  have hev : d 0 + d 4 * alpha^4 = 0 := by
    simpa [evalSeven, Fin.sum_univ_succ, h1, h2, h3, h5, h6] using he
  have hm : d 4 * (alpha^4-1) = 0 := by
    linear_combination hev - hb
  have h4 : d 4 = 0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr ha)
  have h0 : d 0 = 0 := by simpa [h4] using hb
  intro i
  by_cases hi0 : i = 0
  · simpa [hi0] using h0
  by_cases hi4 : i = 4
  · simpa [hi4] using h4
  exact hs i hi0 hi4

#print axioms joint_completion
end AspisV8R19.R853JointCoefficientCompletion
