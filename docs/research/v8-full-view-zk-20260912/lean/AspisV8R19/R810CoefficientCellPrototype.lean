import AspisV8R19.R808PointCoefficientStencil
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk01P0
import AspisV8R19.R780Point02WeightChunk01P2
import AspisV8R19.R760PointWeightChunk00

set_option autoImplicit false
namespace AspisV8R19.R810CoefficientCellPrototype
open AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R802OrdinaryDirectionPointCoefficients
open AspisV8R19.R808PointCoefficientStencil
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem z_eq_source_witness : z = R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl

theorem points0_eq_weight_point : SourceStatementPoints.points z 0 = R780Point02WeightPrototype.point0 := by
  rw [z_eq_source_witness]
  rfl

theorem points2_eq_weight_point : SourceStatementPoints.points z 2 = R780Point02WeightPrototype.point2 := by
  rw [z_eq_source_witness]
  rfl

theorem coeff1_d23_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 1 = 1879053113 := by
  rw [rawRelation_direction_point_decomposition]
  change _ = (1879053113:M)
  rw [show (1:Nat) = relationIndex (0 : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M) * (((536870912:M)*R780Point02WeightPrototype.pw0 92 -
      7*((536870912:M)*R780Point02WeightPrototype.pw0 95)) -
      ((536870912:M)*R780Point02WeightPrototype.pw0 0 - 7*((536870912:M)*R780Point02WeightPrototype.pw0 3))) +
    5^2 * (((536870912:M)*pw 92 - 7*((536870912:M)*pw 95)) -
      ((536870912:M)*pw 0 - 7*((536870912:M)*pw 3))) +
    5^3 * (((536870912:M)*R780Point02WeightPrototype.pw2 92 -
      7*((536870912:M)*R780Point02WeightPrototype.pw2 95)) -
      ((536870912:M)*R780Point02WeightPrototype.pw2 0 - 7*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (1879053113:M)
  rw [R780Point02WeightChunk01P0.pw0_0092, R780Point02WeightChunk01P0.pw0_0095,
    R780Point02WeightChunk00P0.pw0_0000, R780Point02WeightChunk00P0.pw0_0003,
    R760PointWeightChunk00.pw_0092, R760PointWeightChunk00.pw_0095, pw0, pw3,
    R780Point02WeightChunk01P2.pw2_0092, R780Point02WeightChunk01P2.pw2_0095,
    R780Point02WeightChunk00P2.pw2_0000, R780Point02WeightChunk00P2.pw2_0003]
  simp only [R780Point02WeightPrototype.half]
  decide

#print axioms z_eq_source_witness
#print axioms points0_eq_weight_point
#print axioms points2_eq_weight_point
#print axioms coeff1_d23_s0
end
end AspisV8R19.R810CoefficientCellPrototype
