import AspisV8R19.R810CoefficientCellPrototype
import AspisV8R19.R780Point02WeightChunk02P0
import AspisV8R19.R780Point02WeightChunk02P2

set_option autoImplicit false
open AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R802OrdinaryDirectionPointCoefficients
open AspisV8R19.R808PointCoefficientStencil
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R810CoefficientCellPrototype
namespace AspisV8R19.R810CoefficientCellsChunk02
noncomputable section
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem coeff5_d24_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 5 = 0 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) = (0:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^2*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^3*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) = (0:M)
  decide
#print axioms coeff5_d24_s0

theorem coeff5_d24_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 5 = 2147479747 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) = (2147479747:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 97 - (7:M)^2*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw0 1 - (7:M)^2*((0:M)))) + (5:M)^2*(((536870912:M)*pw 97 - (7:M)^2*((0:M))) - ((536870912:M)*pw 1 - (7:M)^2*((0:M)))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 97 - (7:M)^2*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw2 1 - (7:M)^2*((0:M)))) = (2147479747:M)
  rw [R780Point02WeightChunk00P0.pw0_0001, R780Point02WeightChunk02P0.pw0_0097, R780Point02WeightChunk00P2.pw2_0001, R780Point02WeightChunk02P2.pw2_0097, R760PointWeightChunk00.pw_0001, R760PointWeightChunk00.pw_0097]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff5_d24_s1

theorem coeff5_d24_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 5 = 2147465797 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨3,by decide⟩ : Fin 5)) = (2147465797:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 98 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw0 2 - (7:M)^3*((0:M)))) + (5:M)^2*(((536870912:M)*pw 98 - (7:M)^3*((0:M))) - ((536870912:M)*pw 2 - (7:M)^3*((0:M)))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 98 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw2 2 - (7:M)^3*((0:M)))) = (2147465797:M)
  rw [R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk02P0.pw0_0098, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk02P2.pw2_0098, R760PointWeightChunk00.pw_0002, R760PointWeightChunk00.pw_0098]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff5_d24_s2

theorem coeff6_d23_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 6 = 0 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (0:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^2*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^3*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) = (0:M)
  decide
#print axioms coeff6_d23_s0

theorem coeff6_d23_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 6 = 0 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (0:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) + (5:M)^2*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) + (5:M)^3*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) = (0:M)
  decide
#print axioms coeff6_d23_s1

theorem coeff6_d23_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 6 = 536871193 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (536871193:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 93 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw0 1 - (7:M)^3*((0:M)))) + (5:M)^2*(((536870912:M)*pw 93 - (7:M)^3*((0:M))) - ((536870912:M)*pw 1 - (7:M)^3*((0:M)))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 93 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw2 1 - (7:M)^3*((0:M)))) = (536871193:M)
  rw [R780Point02WeightChunk00P0.pw0_0001, R780Point02WeightChunk01P0.pw0_0093, R780Point02WeightChunk00P2.pw2_0001, R780Point02WeightChunk01P2.pw2_0093, R760PointWeightChunk00.pw_0001, R760PointWeightChunk00.pw_0093]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff6_d23_s2

theorem coeff6_d24_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 6 = 0 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (0:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^2*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) + (5:M)^3*(((0:M) - (7:M)^1*((0:M))) - ((0:M) - (7:M)^1*((0:M)))) = (0:M)
  decide
#print axioms coeff6_d24_s0

theorem coeff6_d24_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 6 = 0 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (0:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) + (5:M)^2*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) + (5:M)^3*(((0:M) - (7:M)^2*((0:M))) - ((0:M) - (7:M)^2*((0:M)))) = (0:M)
  decide
#print axioms coeff6_d24_s1

theorem coeff6_d24_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 6 = 2147479747 := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) (536870912:M) 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) (relationIndex (⟨4,by decide⟩ : Fin 5)) = (2147479747:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 97 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw0 1 - (7:M)^3*((0:M)))) + (5:M)^2*(((536870912:M)*pw 97 - (7:M)^3*((0:M))) - ((536870912:M)*pw 1 - (7:M)^3*((0:M)))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 97 - (7:M)^3*((0:M))) - ((536870912:M)*R780Point02WeightPrototype.pw2 1 - (7:M)^3*((0:M)))) = (2147479747:M)
  rw [R780Point02WeightChunk00P0.pw0_0001, R780Point02WeightChunk02P0.pw0_0097, R780Point02WeightChunk00P2.pw2_0001, R780Point02WeightChunk02P2.pw2_0097, R760PointWeightChunk00.pw_0001, R760PointWeightChunk00.pw_0097]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff6_d24_s2
end
end AspisV8R19.R810CoefficientCellsChunk02
