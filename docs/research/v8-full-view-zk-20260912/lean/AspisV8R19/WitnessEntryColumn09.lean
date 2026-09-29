/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient09
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot9_1_0 : (∑ j : Fin 27, q9 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (2046424789:M) := by decide
#print axioms dot9_1_0
theorem dot9_1_1 : (∑ j : Fin 27, q9 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (901996872:M) := by decide
#print axioms dot9_1_1
theorem dot9_1_2 : (∑ j : Fin 27, q9 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1862593164:M) := by decide
#print axioms dot9_1_2
theorem dot9_1_3 : (∑ j : Fin 27, q9 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1951948905:M) := by decide
#print axioms dot9_1_3
theorem dot9_1 : (∑ r : Fin 108, q9 r * WitnessPointData.weights1 r) = (320512789:M) := by
  rw [sum108, dot9_1_0, dot9_1_1, dot9_1_2, dot9_1_3]
  decide
#print axioms dot9_1
theorem dot9_2_0 : (∑ j : Fin 27, q9 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1693619375:M) := by decide
#print axioms dot9_2_0
theorem dot9_2_1 : (∑ j : Fin 27, q9 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1471773585:M) := by decide
#print axioms dot9_2_1
theorem dot9_2_2 : (∑ j : Fin 27, q9 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1463584526:M) := by decide
#print axioms dot9_2_2
theorem dot9_2_3 : (∑ j : Fin 27, q9 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (894290544:M) := by decide
#print axioms dot9_2_3
theorem dot9_2 : (∑ r : Fin 108, q9 r * WitnessPointData.weights2 r) = (1228300736:M) := by
  rw [sum108, dot9_2_0, dot9_2_1, dot9_2_2, dot9_2_3]
  decide
#print axioms dot9_2
theorem poly9_wr_0 : polyCoeff quarter q9 wr 0 = (638997903:M) := by
  rw [poly_slots quarter q9 wr ⟨0,by decide⟩]
  decide
#print axioms poly9_wr_0
theorem poly9_wr_1 : polyCoeff quarter q9 wr 1 = (1885839656:M) := by
  rw [poly_slots quarter q9 wr ⟨1,by decide⟩]
  decide
#print axioms poly9_wr_1
theorem poly9_wr_2 : polyCoeff quarter q9 wr 2 = (720208585:M) := by
  rw [poly_slots quarter q9 wr ⟨2,by decide⟩]
  decide
#print axioms poly9_wr_2
theorem poly9_wr_3 : polyCoeff quarter q9 wr 3 = (1359929660:M) := by
  rw [poly_slots quarter q9 wr ⟨3,by decide⟩]
  decide
#print axioms poly9_wr_3
theorem poly9_wr_4 : polyCoeff quarter q9 wr 4 = (985563134:M) := by
  rw [poly_slots quarter q9 wr ⟨4,by decide⟩]
  decide
#print axioms poly9_wr_4
theorem poly9_wr_5 : polyCoeff quarter q9 wr 5 = (0:M) := by
  rw [poly_slots quarter q9 wr ⟨5,by decide⟩]
  decide
#print axioms poly9_wr_5
theorem poly9_wg_0 : polyCoeff quarter q9 wg 0 = (1440840095:M) := by
  rw [poly_slots quarter q9 wg ⟨0,by decide⟩]
  decide
#print axioms poly9_wg_0
theorem poly9_wg_1 : polyCoeff quarter q9 wg 1 = (882647607:M) := by
  rw [poly_slots quarter q9 wg ⟨1,by decide⟩]
  decide
#print axioms poly9_wg_1
theorem poly9_wg_2 : polyCoeff quarter q9 wg 2 = (532179444:M) := by
  rw [poly_slots quarter q9 wg ⟨2,by decide⟩]
  decide
#print axioms poly9_wg_2
theorem poly9_wg_3 : polyCoeff quarter q9 wg 3 = (992498415:M) := by
  rw [poly_slots quarter q9 wg ⟨3,by decide⟩]
  decide
#print axioms poly9_wg_3
theorem poly9_wg_5 : polyCoeff quarter q9 wg 5 = (0:M) := by
  rw [poly_slots quarter q9 wg ⟨5,by decide⟩]
  decide
#print axioms poly9_wg_5
theorem entry0_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (9:Fin 13) = matrix 0 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot9_1
#print axioms entry0_9
theorem entry1_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (9:Fin 13) = matrix 1 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot9_2
#print axioms entry1_9
theorem entry2_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (9:Fin 13) = matrix 2 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_0
#print axioms entry2_9
theorem entry3_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (9:Fin 13) = matrix 3 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_1
#print axioms entry3_9
theorem entry4_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (9:Fin 13) = matrix 4 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_2
#print axioms entry4_9
theorem entry5_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (9:Fin 13) = matrix 5 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_3
#print axioms entry5_9
theorem entry6_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (9:Fin 13) = matrix 6 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_4
#print axioms entry6_9
theorem entry7_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (9:Fin 13) = matrix 7 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly9_wr_5
#print axioms entry7_9
theorem entry8_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (9:Fin 13) = matrix 8 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly9_wg_0
#print axioms entry8_9
theorem entry9_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (9:Fin 13) = matrix 9 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly9_wg_1
#print axioms entry9_9
theorem entry10_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (9:Fin 13) = matrix 10 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly9_wg_2
#print axioms entry10_9
theorem entry11_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (9:Fin 13) = matrix 11 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly9_wg_3
#print axioms entry11_9
theorem entry12_9 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (9:Fin 13) = matrix 12 9 := by
  simp only [observation, quotient9, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly9_wg_5
#print axioms entry12_9
end
end AspisR19.WitnessEntryData
