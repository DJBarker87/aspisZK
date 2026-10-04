import AspisV8R19.R741SparseCoefficientObservation
import AspisV8R19.R738JointObservationModel

/-! The exact four-slot stencil for the five retained relation coefficients. -/
set_option autoImplicit false
namespace AspisV8R19.R796CoefficientStencil

open AspisR19 AspisR19.BetaUniformCorrection
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open scoped BigOperators
noncomputable section

variable {F : Type*} [CommRing F]

theorem rowWeight_relation_stencil
    (n : Nat) (w : Fin n × Fin 4 → F) (quarter : F)
    (d : Fin n) (k : Fin 5) (slot : Fin 4) :
    rowWeight n (relationIndex k) quarter w d slot =
      if h : slot.val ≤ relationIndex k ∧ relationIndex k - slot.val < 4 then
        quarter * w (d, ⟨(4 - (relationIndex k - slot.val)) % 4,
          Nat.mod_lt _ (by decide)⟩)
      else 0 := by
  fin_cases k <;> fin_cases slot <;>
    simp [rowWeight, relationIndex, Fin.sum_univ_four] <;> ring

#print axioms rowWeight_relation_stencil

end
end AspisV8R19.R796CoefficientStencil
