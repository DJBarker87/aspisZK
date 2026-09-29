/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient10
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot10_1_0 : (∑ j : Fin 27, q10 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (2046934138:M) := by decide
#print axioms dot10_1_0
theorem dot10_1_1 : (∑ j : Fin 27, q10 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (810916414:M) := by decide
#print axioms dot10_1_1
theorem dot10_1_2 : (∑ j : Fin 27, q10 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1481431602:M) := by decide
#print axioms dot10_1_2
theorem dot10_1_3 : (∑ j : Fin 27, q10 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (690227559:M) := by decide
#print axioms dot10_1_3
theorem dot10_1 : (∑ r : Fin 108, q10 r * WitnessPointData.weights1 r) = (734542419:M) := by
  rw [sum108, dot10_1_0, dot10_1_1, dot10_1_2, dot10_1_3]
  decide
#print axioms dot10_1
theorem dot10_2_0 : (∑ j : Fin 27, q10 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (132072466:M) := by decide
#print axioms dot10_2_0
theorem dot10_2_1 : (∑ j : Fin 27, q10 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (859031402:M) := by decide
#print axioms dot10_2_1
theorem dot10_2_2 : (∑ j : Fin 27, q10 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1398990260:M) := by decide
#print axioms dot10_2_2
theorem dot10_2_3 : (∑ j : Fin 27, q10 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (872223566:M) := by decide
#print axioms dot10_2_3
theorem dot10_2 : (∑ r : Fin 108, q10 r * WitnessPointData.weights2 r) = (1114834047:M) := by
  rw [sum108, dot10_2_0, dot10_2_1, dot10_2_2, dot10_2_3]
  decide
#print axioms dot10_2
theorem poly10_wr_0 : polyCoeff quarter q10 wr 0 = (178018027:M) := by
  rw [poly_slots quarter q10 wr ⟨0,by decide⟩]
  decide
#print axioms poly10_wr_0
theorem poly10_wr_1 : polyCoeff quarter q10 wr 1 = (954973613:M) := by
  rw [poly_slots quarter q10 wr ⟨1,by decide⟩]
  decide
#print axioms poly10_wr_1
theorem poly10_wr_2 : polyCoeff quarter q10 wr 2 = (484848810:M) := by
  rw [poly_slots quarter q10 wr ⟨2,by decide⟩]
  decide
#print axioms poly10_wr_2
theorem poly10_wr_3 : polyCoeff quarter q10 wr 3 = (1649781617:M) := by
  rw [poly_slots quarter q10 wr ⟨3,by decide⟩]
  decide
#print axioms poly10_wr_3
theorem poly10_wr_4 : polyCoeff quarter q10 wr 4 = (1816420657:M) := by
  rw [poly_slots quarter q10 wr ⟨4,by decide⟩]
  decide
#print axioms poly10_wr_4
theorem poly10_wr_5 : polyCoeff quarter q10 wr 5 = (985563134:M) := by
  rw [poly_slots quarter q10 wr ⟨5,by decide⟩]
  decide
#print axioms poly10_wr_5
theorem poly10_wg_0 : polyCoeff quarter q10 wg 0 = (1495946077:M) := by
  rw [poly_slots quarter q10 wg ⟨0,by decide⟩]
  decide
#print axioms poly10_wg_0
theorem poly10_wg_1 : polyCoeff quarter q10 wg 1 = (1176922403:M) := by
  rw [poly_slots quarter q10 wg ⟨1,by decide⟩]
  decide
#print axioms poly10_wg_1
theorem poly10_wg_2 : polyCoeff quarter q10 wg 2 = (312936421:M) := by
  rw [poly_slots quarter q10 wg ⟨2,by decide⟩]
  decide
#print axioms poly10_wg_2
theorem poly10_wg_3 : polyCoeff quarter q10 wg 3 = (1037217408:M) := by
  rw [poly_slots quarter q10 wg ⟨3,by decide⟩]
  decide
#print axioms poly10_wg_3
theorem poly10_wg_5 : polyCoeff quarter q10 wg 5 = (828928102:M) := by
  rw [poly_slots quarter q10 wg ⟨5,by decide⟩]
  decide
#print axioms poly10_wg_5
theorem entry0_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (10:Fin 13) = matrix 0 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot10_1
#print axioms entry0_10
theorem entry1_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (10:Fin 13) = matrix 1 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot10_2
#print axioms entry1_10
theorem entry2_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (10:Fin 13) = matrix 2 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_0
#print axioms entry2_10
theorem entry3_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (10:Fin 13) = matrix 3 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_1
#print axioms entry3_10
theorem entry4_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (10:Fin 13) = matrix 4 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_2
#print axioms entry4_10
theorem entry5_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (10:Fin 13) = matrix 5 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_3
#print axioms entry5_10
theorem entry6_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (10:Fin 13) = matrix 6 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_4
#print axioms entry6_10
theorem entry7_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (10:Fin 13) = matrix 7 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly10_wr_5
#print axioms entry7_10
theorem entry8_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (10:Fin 13) = matrix 8 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly10_wg_0
#print axioms entry8_10
theorem entry9_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (10:Fin 13) = matrix 9 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly10_wg_1
#print axioms entry9_10
theorem entry10_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (10:Fin 13) = matrix 10 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly10_wg_2
#print axioms entry10_10
theorem entry11_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (10:Fin 13) = matrix 11 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly10_wg_3
#print axioms entry11_10
theorem entry12_10 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (10:Fin 13) = matrix 12 10 := by
  simp only [observation, quotient10, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly10_wg_5
#print axioms entry12_10
end
end AspisR19.WitnessEntryData
