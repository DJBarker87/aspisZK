/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient03
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot3_1_0 : (∑ j : Fin 27, q3 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (337025324:M) := by decide
#print axioms dot3_1_0
theorem dot3_1_1 : (∑ j : Fin 27, q3 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (421933720:M) := by decide
#print axioms dot3_1_1
theorem dot3_1_2 : (∑ j : Fin 27, q3 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (218269410:M) := by decide
#print axioms dot3_1_2
theorem dot3_1_3 : (∑ j : Fin 27, q3 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (640559244:M) := by decide
#print axioms dot3_1_3
theorem dot3_1 : (∑ r : Fin 108, q3 r * WitnessPointData.weights1 r) = (1617787698:M) := by
  rw [sum108, dot3_1_0, dot3_1_1, dot3_1_2, dot3_1_3]
  decide
#print axioms dot3_1
theorem dot3_2_0 : (∑ j : Fin 27, q3 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1488760822:M) := by decide
#print axioms dot3_2_0
theorem dot3_2_1 : (∑ j : Fin 27, q3 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1978515799:M) := by decide
#print axioms dot3_2_1
theorem dot3_2_2 : (∑ j : Fin 27, q3 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (886682811:M) := by decide
#print axioms dot3_2_2
theorem dot3_2_3 : (∑ j : Fin 27, q3 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (1002464558:M) := by decide
#print axioms dot3_2_3
theorem dot3_2 : (∑ r : Fin 108, q3 r * WitnessPointData.weights2 r) = (1061456696:M) := by
  rw [sum108, dot3_2_0, dot3_2_1, dot3_2_2, dot3_2_3]
  decide
#print axioms dot3_2
theorem poly3_wr_0 : polyCoeff quarter q3 wr 0 = (1023912340:M) := by
  rw [poly_slots quarter q3 wr ⟨0,by decide⟩]
  decide
#print axioms poly3_wr_0
theorem poly3_wr_1 : polyCoeff quarter q3 wr 1 = (1893855740:M) := by
  rw [poly_slots quarter q3 wr ⟨1,by decide⟩]
  decide
#print axioms poly3_wr_1
theorem poly3_wr_2 : polyCoeff quarter q3 wr 2 = (1532857092:M) := by
  rw [poly_slots quarter q3 wr ⟨2,by decide⟩]
  decide
#print axioms poly3_wr_2
theorem poly3_wr_3 : polyCoeff quarter q3 wr 3 = (980483523:M) := by
  rw [poly_slots quarter q3 wr ⟨3,by decide⟩]
  decide
#print axioms poly3_wr_3
theorem poly3_wr_4 : polyCoeff quarter q3 wr 4 = (332515173:M) := by
  rw [poly_slots quarter q3 wr ⟨4,by decide⟩]
  decide
#print axioms poly3_wr_4
theorem poly3_wr_5 : polyCoeff quarter q3 wr 5 = (0:M) := by
  rw [poly_slots quarter q3 wr ⟨5,by decide⟩]
  decide
#print axioms poly3_wr_5
theorem poly3_wg_0 : polyCoeff quarter q3 wg 0 = (2078502351:M) := by
  rw [poly_slots quarter q3 wg ⟨0,by decide⟩]
  decide
#print axioms poly3_wg_0
theorem poly3_wg_1 : polyCoeff quarter q3 wg 1 = (948917344:M) := by
  rw [poly_slots quarter q3 wg ⟨1,by decide⟩]
  decide
#print axioms poly3_wg_1
theorem poly3_wg_2 : polyCoeff quarter q3 wg 2 = (2076539167:M) := by
  rw [poly_slots quarter q3 wg ⟨2,by decide⟩]
  decide
#print axioms poly3_wg_2
theorem poly3_wg_3 : polyCoeff quarter q3 wg 3 = (1682393913:M) := by
  rw [poly_slots quarter q3 wg ⟨3,by decide⟩]
  decide
#print axioms poly3_wg_3
theorem poly3_wg_5 : polyCoeff quarter q3 wg 5 = (0:M) := by
  rw [poly_slots quarter q3 wg ⟨5,by decide⟩]
  decide
#print axioms poly3_wg_5
theorem entry0_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (3:Fin 13) = matrix 0 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot3_1
#print axioms entry0_3
theorem entry1_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (3:Fin 13) = matrix 1 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot3_2
#print axioms entry1_3
theorem entry2_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (3:Fin 13) = matrix 2 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_0
#print axioms entry2_3
theorem entry3_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (3:Fin 13) = matrix 3 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_1
#print axioms entry3_3
theorem entry4_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (3:Fin 13) = matrix 4 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_2
#print axioms entry4_3
theorem entry5_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (3:Fin 13) = matrix 5 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_3
#print axioms entry5_3
theorem entry6_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (3:Fin 13) = matrix 6 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_4
#print axioms entry6_3
theorem entry7_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (3:Fin 13) = matrix 7 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly3_wr_5
#print axioms entry7_3
theorem entry8_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (3:Fin 13) = matrix 8 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly3_wg_0
#print axioms entry8_3
theorem entry9_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (3:Fin 13) = matrix 9 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly3_wg_1
#print axioms entry9_3
theorem entry10_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (3:Fin 13) = matrix 10 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly3_wg_2
#print axioms entry10_3
theorem entry11_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (3:Fin 13) = matrix 11 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly3_wg_3
#print axioms entry11_3
theorem entry12_3 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (3:Fin 13) = matrix 12 3 := by
  simp only [observation, quotient3, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly3_wg_5
#print axioms entry12_3
end
end AspisR19.WitnessEntryData
