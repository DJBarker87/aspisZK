import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace AspisV8R11
variable {K U V W Y : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]

theorem selected_coins_for_fixed_first_message
    (A : U ≃ₗ[K] V) (F : W →ₗ[K] V) (u : U) (v : W) (q : V)
    (first : A u + F v = q) : u = A.symm (q - F v) := by
  apply A.injective
  rw [A.apply_symm_apply]
  exact eq_sub_iff_add_eq.mpr first

theorem later_view_after_selected_elimination
    (A : U ≃ₗ[K] V) (F : W →ₗ[K] V)
    (B : U →ₗ[K] Y) (D : W →ₗ[K] Y)
    (u : U) (v : W) (q : V) (t : Y)
    (first : A u + F v = q) :
    t + B u + D v =
      (t + B (A.symm q)) + (D v - B (A.symm (F v))) := by
  rw [selected_coins_for_fixed_first_message A F u v q first]
  simp only [map_sub]
  abel

#print axioms selected_coins_for_fixed_first_message
#print axioms later_view_after_selected_elimination
end AspisV8R11
