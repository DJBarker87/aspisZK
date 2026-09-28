/- Reuse the earlier posterior-elimination identity. This is a coverage
   equivalence, not a probability/simulator claim or assumed residual rank. -/
import AspisV8R11.PosteriorElimination

namespace AspisR19.GResidualSchur
open AspisV8R11
variable {K U V W Y : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]

theorem reconstruct_core (A : U ≃ₗ[K] V) (F : W →ₗ[K] V)
    (a : V) (v : W) : A (A.symm (a-F v)) + F v=a := by
  rw [A.apply_symm_apply,sub_add_cancel]

theorem residual_equivalence (A : U ≃ₗ[K] V) (F : W →ₗ[K] V)
    (B : U →ₗ[K] Y) (D : W →ₗ[K] Y) (a : V) (b : Y) :
    (∃ u v, A u+F v=a ∧ B u+D v=b) ↔
      ∃ v, D v-B (A.symm (F v))=b-B (A.symm a) := by
  constructor
  · rintro ⟨u,v,ha,hb⟩
    refine ⟨v,?_⟩
    have h := later_view_after_selected_elimination A F B D u v a 0 ha
    simp only [zero_add] at h
    rw [hb] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)
  · rintro ⟨v,hv⟩
    refine ⟨A.symm (a-F v),v,reconstruct_core A F a v,?_⟩
    have h := later_view_after_selected_elimination A F B D
      (A.symm (a-F v)) v a 0 (reconstruct_core A F a v)
    simp only [zero_add] at h
    rw [h,hv]
    exact add_sub_cancel _ _

#print axioms reconstruct_core
#print axioms residual_equivalence
end AspisR19.GResidualSchur
