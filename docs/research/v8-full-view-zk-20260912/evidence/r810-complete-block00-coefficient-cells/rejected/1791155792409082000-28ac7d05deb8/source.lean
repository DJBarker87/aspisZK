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
namespace AspisV8R19.R810CoefficientCellsChunk00
noncomputable section
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem coeff1_d23_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 1 = 268469909 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (1:Nat) = relationIndex (⟨0,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 95)) - ((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 3))) + (5:M)^2*(((0:M) - (7:M)^2*((536870912:M)*pw 95)) - ((0:M) - (7:M)^2*((536870912:M)*pw 3))) + (5:M)^3*(((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 95)) - ((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (268469909:M)
  rw [R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk01P0.pw0_0095, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk01P2.pw2_0095, pw3, R760PointWeightChunk00.pw_0095]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff1_d23_s1

theorem coeff1_d23_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 1 = 1879289363 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (1:Nat) = relationIndex (⟨0,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 95)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 3))) + (5:M)^2*(((0:M) - (7:M)^3*((536870912:M)*pw 95)) - ((0:M) - (7:M)^3*((536870912:M)*pw 3))) + (5:M)^3*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 95)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (1879289363:M)
  rw [R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk01P0.pw0_0095, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk01P2.pw2_0095, pw3, R760PointWeightChunk00.pw_0095]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff1_d23_s2

theorem coeff1_d24_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 1 = 2147362972 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (1:Nat) = relationIndex (⟨0,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 96 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 99)) - ((536870912:M)*R780Point02WeightPrototype.pw0 0 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 3))) + (5:M)^2*(((536870912:M)*pw 96 - (7:M)^1*((536870912:M)*pw 99)) - ((536870912:M)*pw 0 - (7:M)^1*((536870912:M)*pw 3))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 96 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 99)) - ((536870912:M)*R780Point02WeightPrototype.pw2 0 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (2147362972:M)
  rw [R780Point02WeightChunk00P0.pw0_0000, R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk02P0.pw0_0096, R780Point02WeightChunk02P0.pw0_0099, R780Point02WeightChunk00P2.pw2_0000, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk02P2.pw2_0096, R780Point02WeightChunk02P2.pw2_0099, pw0, pw3, R760PointWeightChunk00.pw_0096, R760PointWeightChunk00.pw_0099]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff1_d24_s0

theorem coeff1_d24_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 1 = 2146642072 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (1:Nat) = relationIndex (⟨0,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 99)) - ((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 3))) + (5:M)^2*(((0:M) - (7:M)^2*((536870912:M)*pw 99)) - ((0:M) - (7:M)^2*((536870912:M)*pw 3))) + (5:M)^3*(((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 99)) - ((0:M) - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (2146642072:M)
  rw [R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk02P0.pw0_0099, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk02P2.pw2_0099, pw3, R760PointWeightChunk00.pw_0099]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff1_d24_s1

theorem coeff1_d24_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 1 = 2141592622 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (1:Nat) = relationIndex (⟨0,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 99)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 3))) + (5:M)^2*(((0:M) - (7:M)^3*((536870912:M)*pw 99)) - ((0:M) - (7:M)^3*((536870912:M)*pw 3))) + (5:M)^3*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 99)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 3))) = (2141592622:M)
  rw [R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk02P0.pw0_0099, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk02P2.pw2_0099, pw3, R760PointWeightChunk00.pw_0099]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff1_d24_s2

theorem coeff2_d23_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 2 = 268432784 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (2:Nat) = relationIndex (⟨1,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 95 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 94)) - ((536870912:M)*R780Point02WeightPrototype.pw0 3 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 2))) + (5:M)^2*(((536870912:M)*pw 95 - (7:M)^1*((536870912:M)*pw 94)) - ((536870912:M)*pw 3 - (7:M)^1*((536870912:M)*pw 2))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 95 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 94)) - ((536870912:M)*R780Point02WeightPrototype.pw2 3 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 2))) = (268432784:M)
  rw [R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk01P0.pw0_0094, R780Point02WeightChunk01P0.pw0_0095, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk01P2.pw2_0094, R780Point02WeightChunk01P2.pw2_0095, R760PointWeightChunk00.pw_0002, pw3, R760PointWeightChunk00.pw_0094, R760PointWeightChunk00.pw_0095]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff2_d23_s0

theorem coeff2_d23_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 2 = 1610598954 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (2:Nat) = relationIndex (⟨1,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 92 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 94)) - ((536870912:M)*R780Point02WeightPrototype.pw0 0 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 2))) + (5:M)^2*(((536870912:M)*pw 92 - (7:M)^2*((536870912:M)*pw 94)) - ((536870912:M)*pw 0 - (7:M)^2*((536870912:M)*pw 2))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 92 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 94)) - ((536870912:M)*R780Point02WeightPrototype.pw2 0 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 2))) = (1610598954:M)
  rw [R780Point02WeightChunk00P0.pw0_0000, R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk01P0.pw0_0092, R780Point02WeightChunk01P0.pw0_0094, R780Point02WeightChunk00P2.pw2_0000, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk01P2.pw2_0092, R780Point02WeightChunk01P2.pw2_0094, pw0, R760PointWeightChunk00.pw_0002, R760PointWeightChunk00.pw_0092, R760PointWeightChunk00.pw_0094]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff2_d23_s1

theorem coeff2_d23_s2 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 2 = 536774443 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (2:Nat) = relationIndex (⟨1,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 94)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw0 2))) + (5:M)^2*(((0:M) - (7:M)^3*((536870912:M)*pw 94)) - ((0:M) - (7:M)^3*((536870912:M)*pw 2))) + (5:M)^3*(((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 94)) - ((0:M) - (7:M)^3*((536870912:M)*R780Point02WeightPrototype.pw2 2))) = (536774443:M)
  rw [R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk01P0.pw0_0094, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk01P2.pw2_0094, R760PointWeightChunk00.pw_0002, R760PointWeightChunk00.pw_0094]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff2_d23_s2

theorem coeff2_d24_s0 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 2 = 142125 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (2:Nat) = relationIndex (⟨1,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 99 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 98)) - ((536870912:M)*R780Point02WeightPrototype.pw0 3 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw0 2))) + (5:M)^2*(((536870912:M)*pw 99 - (7:M)^1*((536870912:M)*pw 98)) - ((536870912:M)*pw 3 - (7:M)^1*((536870912:M)*pw 2))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 99 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 98)) - ((536870912:M)*R780Point02WeightPrototype.pw2 3 - (7:M)^1*((536870912:M)*R780Point02WeightPrototype.pw2 2))) = (142125:M)
  rw [R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk00P0.pw0_0003, R780Point02WeightChunk02P0.pw0_0098, R780Point02WeightChunk02P0.pw0_0099, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk00P2.pw2_0003, R780Point02WeightChunk02P2.pw2_0098, R780Point02WeightChunk02P2.pw2_0099, R760PointWeightChunk00.pw_0002, pw3, R760PointWeightChunk00.pw_0098, R760PointWeightChunk00.pw_0099]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff2_d24_s0

theorem coeff2_d24_s1 :
    rawRelation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 2 = 874200 := by
  rw [rawRelation_direction_point_decomposition]
  rw [show (2:Nat) = relationIndex (⟨1,by decide⟩ : Fin 5) from rfl]
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*(((536870912:M)*R780Point02WeightPrototype.pw0 96 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 98)) - ((536870912:M)*R780Point02WeightPrototype.pw0 0 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw0 2))) + (5:M)^2*(((536870912:M)*pw 96 - (7:M)^2*((536870912:M)*pw 98)) - ((536870912:M)*pw 0 - (7:M)^2*((536870912:M)*pw 2))) + (5:M)^3*(((536870912:M)*R780Point02WeightPrototype.pw2 96 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 98)) - ((536870912:M)*R780Point02WeightPrototype.pw2 0 - (7:M)^2*((536870912:M)*R780Point02WeightPrototype.pw2 2))) = (874200:M)
  rw [R780Point02WeightChunk00P0.pw0_0000, R780Point02WeightChunk00P0.pw0_0002, R780Point02WeightChunk02P0.pw0_0096, R780Point02WeightChunk02P0.pw0_0098, R780Point02WeightChunk00P2.pw2_0000, R780Point02WeightChunk00P2.pw2_0002, R780Point02WeightChunk02P2.pw2_0096, R780Point02WeightChunk02P2.pw2_0098, pw0, R760PointWeightChunk00.pw_0002, R760PointWeightChunk00.pw_0096, R760PointWeightChunk00.pw_0098]
  simp only [R780Point02WeightPrototype.half]
  decide
#print axioms coeff2_d24_s1
end
end AspisV8R19.R810CoefficientCellsChunk00
