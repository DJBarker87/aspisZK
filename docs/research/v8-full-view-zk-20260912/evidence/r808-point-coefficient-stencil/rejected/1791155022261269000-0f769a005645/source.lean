import AspisV8R19.R802OrdinaryDirectionPointCoefficients
import AspisV8R19.R796CoefficientStencil

set_option autoImplicit false
namespace AspisV8R19.R808PointCoefficientStencil
open AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R802OrdinaryDirectionPointCoefficients
open AspisV8R19.R796CoefficientStencil
noncomputable section
variable {F : Type*} [CommRing F]

def pointStencil (quarter : F) (w : Nat → F) (d : Fin 255) (slot : Fin 4) (k : Fin 5) : F :=
  if slot.val ≤ relationIndex k ∧ relationIndex k - slot.val < 4 then
    quarter * w (4*d.val + (4 - (relationIndex k - slot.val)) % 4)
  else 0

theorem pointCoefficient_direction_stencil
    (half quarter a b c alpha : F) (point : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) (k : Fin 5) :
    pointCoefficient half quarter a b c point (indexedDirection alpha d s) (relationIndex k) =
      (pointStencil quarter (pointWeight half a b c point) d ⟨s.val+1,by omega⟩ k -
        alpha^(s.val+1) * pointStencil quarter (pointWeight half a b c point) d 0 k) -
      (pointStencil quarter (pointWeight half a b c point) 0 ⟨s.val+1,by omega⟩ k -
        alpha^(s.val+1) * pointStencil quarter (pointWeight half a b c point) 0 0 k) := by
  unfold pointCoefficient indexedDirection
  simp only [coefficient_direction, rowWeight_relation_stencil, pointStencil, cast255,
    Fin.val_mk, Fin.val_zero, Nat.mul_zero, zero_add]

#print axioms pointCoefficient_direction_stencil
end
end AspisV8R19.R808PointCoefficientStencil
