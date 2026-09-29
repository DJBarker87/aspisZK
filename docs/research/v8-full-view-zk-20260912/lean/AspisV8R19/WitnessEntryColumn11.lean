/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient11
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot11_1_0 : (∑ j : Fin 27, q11 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (486857120:M) := by decide
#print axioms dot11_1_0
theorem dot11_1_1 : (∑ j : Fin 27, q11 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (603680653:M) := by decide
#print axioms dot11_1_1
theorem dot11_1_2 : (∑ j : Fin 27, q11 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (123320061:M) := by decide
#print axioms dot11_1_2
theorem dot11_1_3 : (∑ j : Fin 27, q11 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (973704446:M) := by decide
#print axioms dot11_1_3
theorem dot11_1 : (∑ r : Fin 108, q11 r * WitnessPointData.weights1 r) = (40078633:M) := by
  rw [sum108, dot11_1_0, dot11_1_1, dot11_1_2, dot11_1_3]
  decide
#print axioms dot11_1
theorem dot11_2_0 : (∑ j : Fin 27, q11 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (880849813:M) := by decide
#print axioms dot11_2_0
theorem dot11_2_1 : (∑ j : Fin 27, q11 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1149438169:M) := by decide
#print axioms dot11_2_1
theorem dot11_2_2 : (∑ j : Fin 27, q11 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (872624724:M) := by decide
#print axioms dot11_2_2
theorem dot11_2_3 : (∑ j : Fin 27, q11 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (646899319:M) := by decide
#print axioms dot11_2_3
theorem dot11_2 : (∑ r : Fin 108, q11 r * WitnessPointData.weights2 r) = (1402328378:M) := by
  rw [sum108, dot11_2_0, dot11_2_1, dot11_2_2, dot11_2_3]
  decide
#print axioms dot11_2
theorem poly11_wr_0 : polyCoeff quarter q11 wr 0 = (1246126189:M) := by
  rw [poly_slots quarter q11 wr ⟨0,by decide⟩]
  decide
#print axioms poly11_wr_0
theorem poly11_wr_1 : polyCoeff quarter q11 wr 1 = (242364350:M) := by
  rw [poly_slots quarter q11 wr ⟨1,by decide⟩]
  decide
#print axioms poly11_wr_1
theorem poly11_wr_2 : polyCoeff quarter q11 wr 2 = (1885455926:M) := by
  rw [poly_slots quarter q11 wr ⟨2,by decide⟩]
  decide
#print axioms poly11_wr_2
theorem poly11_wr_3 : polyCoeff quarter q11 wr 3 = (549409093:M) := by
  rw [poly_slots quarter q11 wr ⟨3,by decide⟩]
  decide
#print axioms poly11_wr_3
theorem poly11_wr_4 : polyCoeff quarter q11 wr 4 = (550251302:M) := by
  rw [poly_slots quarter q11 wr ⟨4,by decide⟩]
  decide
#print axioms poly11_wr_4
theorem poly11_wr_5 : polyCoeff quarter q11 wr 5 = (1816420657:M) := by
  rw [poly_slots quarter q11 wr ⟨5,by decide⟩]
  decide
#print axioms poly11_wr_5
theorem poly11_wg_0 : polyCoeff quarter q11 wg 0 = (1881687951:M) := by
  rw [poly_slots quarter q11 wg ⟨0,by decide⟩]
  decide
#print axioms poly11_wg_0
theorem poly11_wg_1 : polyCoeff quarter q11 wg 1 = (1796005880:M) := by
  rw [poly_slots quarter q11 wg ⟨1,by decide⟩]
  decide
#print axioms poly11_wg_1
theorem poly11_wg_2 : polyCoeff quarter q11 wg 2 = (1483911395:M) := by
  rw [poly_slots quarter q11 wg ⟨2,by decide⟩]
  decide
#print axioms poly11_wg_2
theorem poly11_wg_3 : polyCoeff quarter q11 wg 3 = (1700718522:M) := by
  rw [poly_slots quarter q11 wg ⟨3,by decide⟩]
  decide
#print axioms poly11_wg_3
theorem poly11_wg_5 : polyCoeff quarter q11 wg 5 = (352544188:M) := by
  rw [poly_slots quarter q11 wg ⟨5,by decide⟩]
  decide
#print axioms poly11_wg_5
theorem entry0_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (11:Fin 13) = matrix 0 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot11_1
#print axioms entry0_11
theorem entry1_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (11:Fin 13) = matrix 1 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot11_2
#print axioms entry1_11
theorem entry2_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (11:Fin 13) = matrix 2 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_0
#print axioms entry2_11
theorem entry3_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (11:Fin 13) = matrix 3 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_1
#print axioms entry3_11
theorem entry4_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (11:Fin 13) = matrix 4 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_2
#print axioms entry4_11
theorem entry5_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (11:Fin 13) = matrix 5 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_3
#print axioms entry5_11
theorem entry6_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (11:Fin 13) = matrix 6 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_4
#print axioms entry6_11
theorem entry7_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (11:Fin 13) = matrix 7 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly11_wr_5
#print axioms entry7_11
theorem entry8_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (11:Fin 13) = matrix 8 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly11_wg_0
#print axioms entry8_11
theorem entry9_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (11:Fin 13) = matrix 9 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly11_wg_1
#print axioms entry9_11
theorem entry10_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (11:Fin 13) = matrix 10 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly11_wg_2
#print axioms entry10_11
theorem entry11_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (11:Fin 13) = matrix 11 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly11_wg_3
#print axioms entry11_11
theorem entry12_11 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (11:Fin 13) = matrix 12 11 := by
  simp only [observation, quotient11, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly11_wg_5
#print axioms entry12_11
end
end AspisR19.WitnessEntryData
