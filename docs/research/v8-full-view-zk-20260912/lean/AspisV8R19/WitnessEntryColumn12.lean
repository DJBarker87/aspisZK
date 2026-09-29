/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient12
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot12_1_0 : (∑ j : Fin 27, q12 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (793350605:M) := by decide
#print axioms dot12_1_0
theorem dot12_1_1 : (∑ j : Fin 27, q12 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (1904135954:M) := by decide
#print axioms dot12_1_1
theorem dot12_1_2 : (∑ j : Fin 27, q12 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1907771143:M) := by decide
#print axioms dot12_1_2
theorem dot12_1_3 : (∑ j : Fin 27, q12 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1676381429:M) := by decide
#print axioms dot12_1_3
theorem dot12_1 : (∑ r : Fin 108, q12 r * WitnessPointData.weights1 r) = (1986671837:M) := by
  rw [sum108, dot12_1_0, dot12_1_1, dot12_1_2, dot12_1_3]
  decide
#print axioms dot12_1
theorem dot12_2_0 : (∑ j : Fin 27, q12 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1089773395:M) := by decide
#print axioms dot12_2_0
theorem dot12_2_1 : (∑ j : Fin 27, q12 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1228938228:M) := by decide
#print axioms dot12_2_1
theorem dot12_2_2 : (∑ j : Fin 27, q12 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1252211867:M) := by decide
#print axioms dot12_2_2
theorem dot12_2_3 : (∑ j : Fin 27, q12 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (1642857342:M) := by decide
#print axioms dot12_2_3
theorem dot12_2 : (∑ r : Fin 108, q12 r * WitnessPointData.weights2 r) = (918813538:M) := by
  rw [sum108, dot12_2_0, dot12_2_1, dot12_2_2, dot12_2_3]
  decide
#print axioms dot12_2
theorem poly12_wr_0 : polyCoeff quarter q12 wr 0 = (434885649:M) := by
  rw [poly_slots quarter q12 wr ⟨0,by decide⟩]
  decide
#print axioms poly12_wr_0
theorem poly12_wr_1 : polyCoeff quarter q12 wr 1 = (1856562103:M) := by
  rw [poly_slots quarter q12 wr ⟨1,by decide⟩]
  decide
#print axioms poly12_wr_1
theorem poly12_wr_2 : polyCoeff quarter q12 wr 2 = (1910432818:M) := by
  rw [poly_slots quarter q12 wr ⟨2,by decide⟩]
  decide
#print axioms poly12_wr_2
theorem poly12_wr_3 : polyCoeff quarter q12 wr 3 = (310985834:M) := by
  rw [poly_slots quarter q12 wr ⟨3,by decide⟩]
  decide
#print axioms poly12_wr_3
theorem poly12_wr_4 : polyCoeff quarter q12 wr 4 = (1233826799:M) := by
  rw [poly_slots quarter q12 wr ⟨4,by decide⟩]
  decide
#print axioms poly12_wr_4
theorem poly12_wr_5 : polyCoeff quarter q12 wr 5 = (0:M) := by
  rw [poly_slots quarter q12 wr ⟨5,by decide⟩]
  decide
#print axioms poly12_wr_5
theorem poly12_wg_0 : polyCoeff quarter q12 wg 0 = (2040796927:M) := by
  rw [poly_slots quarter q12 wg ⟨0,by decide⟩]
  decide
#print axioms poly12_wg_0
theorem poly12_wg_1 : polyCoeff quarter q12 wg 1 = (1820210563:M) := by
  rw [poly_slots quarter q12 wg ⟨1,by decide⟩]
  decide
#print axioms poly12_wg_1
theorem poly12_wg_2 : polyCoeff quarter q12 wg 2 = (1635781994:M) := by
  rw [poly_slots quarter q12 wg ⟨2,by decide⟩]
  decide
#print axioms poly12_wg_2
theorem poly12_wg_3 : polyCoeff quarter q12 wg 3 = (2114136312:M) := by
  rw [poly_slots quarter q12 wg ⟨3,by decide⟩]
  decide
#print axioms poly12_wg_3
theorem poly12_wg_5 : polyCoeff quarter q12 wg 5 = (0:M) := by
  rw [poly_slots quarter q12 wg ⟨5,by decide⟩]
  decide
#print axioms poly12_wg_5
theorem entry0_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (12:Fin 13) = matrix 0 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot12_1
#print axioms entry0_12
theorem entry1_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (12:Fin 13) = matrix 1 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot12_2
#print axioms entry1_12
theorem entry2_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (12:Fin 13) = matrix 2 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_0
#print axioms entry2_12
theorem entry3_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (12:Fin 13) = matrix 3 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_1
#print axioms entry3_12
theorem entry4_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (12:Fin 13) = matrix 4 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_2
#print axioms entry4_12
theorem entry5_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (12:Fin 13) = matrix 5 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_3
#print axioms entry5_12
theorem entry6_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (12:Fin 13) = matrix 6 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_4
#print axioms entry6_12
theorem entry7_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (12:Fin 13) = matrix 7 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly12_wr_5
#print axioms entry7_12
theorem entry8_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (12:Fin 13) = matrix 8 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly12_wg_0
#print axioms entry8_12
theorem entry9_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (12:Fin 13) = matrix 9 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly12_wg_1
#print axioms entry9_12
theorem entry10_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (12:Fin 13) = matrix 10 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly12_wg_2
#print axioms entry10_12
theorem entry11_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (12:Fin 13) = matrix 11 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly12_wg_3
#print axioms entry11_12
theorem entry12_12 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (12:Fin 13) = matrix 12 12 := by
  simp only [observation, quotient12, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly12_wg_5
#print axioms entry12_12
end
end AspisR19.WitnessEntryData
