import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The six-constant identity for three fixed chord component maps.
Instantiation of these linear maps with Rust routines is not assumed here. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F V : Type*} [CommRing F] [AddCommGroup V] [Module F V]

theorem active_linear_form (L : Fin 3 → V →ₗ[F] F)
    (chord : Fin 3 → F) (channel base : V) (alpha : F) (k : ℕ) :
    (∑ j : Fin 3, chord j * L j (channel - alpha^k • base)) =
      ∑ j : Fin 3, chord j * (L j channel - alpha^k * L j base) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sub, map_smul]
  rfl

/-- Fixed finite coefficient maps are linear; this is the shape of each
source basis multiplication followed by active coefficient projection. -/
def coefficientForm {I : Type*} [Fintype I] (weights : I → F) : (I → F) →ₗ[F] F where
  toFun q := ∑ i, weights i * q i
  map_add' q r := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c q := by simp [Finset.mul_sum, mul_left_comm]

#print axioms active_linear_form
#print axioms coefficientForm
end AspisV8R17
