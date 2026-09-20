import Mathlib.Algebra.Group.Hom.Defs

/-! A necessary condition for the source's single shared-functional batch.
This does not constitute an attack on the unchanged protocol. -/
set_option autoImplicit false
namespace AspisV8R17
variable {V F : Type*} [AddCommGroup V] [AddCommGroup F]

theorem shared_batch_requires_same_functional (a b : V →+ F) (combined : V → F)
    (h : ∀ u v, combined (u+v) = a u + b v) : a = b := by
  ext v
  have ha := h v 0
  have hb := h 0 v
  simp only [add_zero, zero_add, map_zero] at ha hb
  exact ha.symm.trans hb

theorem distinct_functionals_no_shared_batch (a b : V →+ F) (hne : a ≠ b) :
    ¬ ∃ combined : V → F, ∀ u v, combined (u+v) = a u + b v := by
  rintro ⟨combined,h⟩
  exact hne (shared_batch_requires_same_functional a b combined h)

#print axioms shared_batch_requires_same_functional
#print axioms distinct_functionals_no_shared_batch
end AspisV8R17
