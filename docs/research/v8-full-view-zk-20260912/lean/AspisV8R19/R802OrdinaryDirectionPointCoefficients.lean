import AspisV8R19.R795OrdinaryCoefficientDecomposition
import AspisV8R19.R743JointSparseEntryBinding

set_option autoImplicit false
namespace AspisV8R19.R802OrdinaryDirectionPointCoefficients
open AspisR19 AspisR19.BetaUniformCorrection AspisR19.FullCoefficientBoundary
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R795OrdinaryCoefficientDecomposition
noncomputable section
variable {F : Type*} [CommRing F]

def pointCoefficient (half quarter a b c : F) (point : Fin 10 → F)
    (q : R738JointObservationModel.Index256 → F) (k : Nat) : F :=
  coefficient (sourceKernel 256 k quarter) q
    (fun i => pointWeight half a b c point (4*i.1.val+i.2.val))

theorem rawRelation_direction_point_decomposition
    (half quarter a b c alpha kappa tau : F) (z : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) (k : Nat) :
    rawRelation half quarter a b c kappa tau z (indexedDirection alpha d s) k =
      kappa * pointCoefficient half quarter a b c (SourceStatementPoints.points z 0)
        (indexedDirection alpha d s) k +
      kappa^2 * pointCoefficient half quarter a b c (SourceStatementPoints.points z 1)
        (indexedDirection alpha d s) k +
      kappa^3 * pointCoefficient half quarter a b c (SourceStatementPoints.points z 2)
        (indexedDirection alpha d s) k := by
  unfold rawRelation pointCoefficient indexedDirection
  simp only [coefficient_direction]
  have hz : (0 : Fin 256) = cast255 (0 : Fin 255) := rfl
  rw [hz]
  simp only [rowWeight_raw_ordinary_decomposition]
  ring

#print axioms rawRelation_direction_point_decomposition
end
end AspisV8R19.R802OrdinaryDirectionPointCoefficients
