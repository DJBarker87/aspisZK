import AspisV8R19.R795OrdinaryCoefficientDecomposition
import AspisV8R19.R743JointSparseEntryBinding

set_option autoImplicit false
namespace AspisV8R19.R866OrdinaryBlockKernel
open AspisR19 AspisR19.BetaUniformCorrection AspisR19.FullCoefficientBoundary
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R795OrdinaryCoefficientDecomposition
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

theorem rowWeight_eq_of_block_eq (k : Nat) (quarter : F)
    (w : Fin 256 × Fin 4 → F) (d : Fin 256)
    (hblock : ∀ t : Fin 4, w (d,t) = w (0,t)) (slot : Fin 4) :
    rowWeight 256 k quarter w d slot = rowWeight 256 k quarter w 0 slot := by
  unfold rowWeight
  apply Finset.sum_congr rfl
  intro t _
  rw [hblock t]

theorem ordinary_block_eq (half a b c kappa tau : F) (z : Fin 10 → F)
    (d : Fin 255)
    (hpoints : ∀ p : Fin 3, ∀ t : Fin 4,
      pointWeight half a b c (SourceStatementPoints.points z p) (4*d.val+t.val) =
        pointWeight half a b c (SourceStatementPoints.points z p) t.val)
    (t : Fin 4) :
    rawOrdinaryWeight half a b c kappa tau z (4*d.val+t.val) =
      rawOrdinaryWeight half a b c kappa tau z t.val := by
  rw [raw_ordinary_weight_below half a b c kappa tau z (by have := d.isLt; have := t.isLt; omega),
    raw_ordinary_weight_below half a b c kappa tau z (by have := t.isLt; omega)]
  rw [hpoints 0 t, hpoints 1 t, hpoints 2 t]

theorem all_ordinary_coefficients_zero (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3)
    (hpoints : ∀ p : Fin 3, ∀ t : Fin 4,
      pointWeight half a b c (SourceStatementPoints.points z p) (4*d.val+t.val) =
        pointWeight half a b c (SourceStatementPoints.points z p) t.val)
    (k : Nat) :
    rawRelation half quarter a b c kappa tau z (indexedDirection alpha d s) k = 0 := by
  unfold rawRelation indexedDirection
  rw [coefficient_direction]
  have hb : ∀ t : Fin 4,
      (fun i : Fin 256 × Fin 4 => rawOrdinaryWeight half a b c kappa tau z
        (4*i.1.val+i.2.val)) (cast255 d,t) =
      (fun i : Fin 256 × Fin 4 => rawOrdinaryWeight half a b c kappa tau z
        (4*i.1.val+i.2.val)) (0,t) := by
    intro t
    simpa only [cast255, Fin.val_zero, Nat.mul_zero, Nat.zero_add] using
      ordinary_block_eq half a b c kappa tau z d hpoints t
  rw [rowWeight_eq_of_block_eq k quarter _ (cast255 d) hb,
    rowWeight_eq_of_block_eq k quarter _ (cast255 d) hb]
  exact sub_self _

#print axioms rowWeight_eq_of_block_eq
#print axioms ordinary_block_eq
#print axioms all_ordinary_coefficients_zero
end
end AspisV8R19.R866OrdinaryBlockKernel
