/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient02
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot2_1_0 : (∑ j : Fin 27, q2 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (1492578605:M) := by decide
#print axioms dot2_1_0
theorem dot2_1_1 : (∑ j : Fin 27, q2 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (824531420:M) := by decide
#print axioms dot2_1_1
theorem dot2_1_2 : (∑ j : Fin 27, q2 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1289852557:M) := by decide
#print axioms dot2_1_2
theorem dot2_1_3 : (∑ j : Fin 27, q2 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (281182303:M) := by decide
#print axioms dot2_1_3
theorem dot2_1 : (∑ r : Fin 108, q2 r * WitnessPointData.weights1 r) = (1740661238:M) := by
  rw [sum108, dot2_1_0, dot2_1_1, dot2_1_2, dot2_1_3]
  decide
#print axioms dot2_1
theorem dot2_2_0 : (∑ j : Fin 27, q2 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1318496811:M) := by decide
#print axioms dot2_2_0
theorem dot2_2_1 : (∑ j : Fin 27, q2 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (251118234:M) := by decide
#print axioms dot2_2_1
theorem dot2_2_2 : (∑ j : Fin 27, q2 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (890552042:M) := by decide
#print axioms dot2_2_2
theorem dot2_2_3 : (∑ j : Fin 27, q2 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (1962793397:M) := by decide
#print axioms dot2_2_3
theorem dot2_2 : (∑ r : Fin 108, q2 r * WitnessPointData.weights2 r) = (127993190:M) := by
  rw [sum108, dot2_2_0, dot2_2_1, dot2_2_2, dot2_2_3]
  decide
#print axioms dot2_2
theorem poly2_wr_0 : polyCoeff quarter q2 wr 0 = (304811154:M) := by
  rw [poly_slots quarter q2 wr ⟨0,by decide⟩]
  decide
#print axioms poly2_wr_0
theorem poly2_wr_1 : polyCoeff quarter q2 wr 1 = (695177590:M) := by
  rw [poly_slots quarter q2 wr ⟨1,by decide⟩]
  decide
#print axioms poly2_wr_1
theorem poly2_wr_2 : polyCoeff quarter q2 wr 2 = (1014276428:M) := by
  rw [poly_slots quarter q2 wr ⟨2,by decide⟩]
  decide
#print axioms poly2_wr_2
theorem poly2_wr_3 : polyCoeff quarter q2 wr 3 = (413895901:M) := by
  rw [poly_slots quarter q2 wr ⟨3,by decide⟩]
  decide
#print axioms poly2_wr_3
theorem poly2_wr_4 : polyCoeff quarter q2 wr 4 = (624061770:M) := by
  rw [poly_slots quarter q2 wr ⟨4,by decide⟩]
  decide
#print axioms poly2_wr_4
theorem poly2_wr_5 : polyCoeff quarter q2 wr 5 = (1073915192:M) := by
  rw [poly_slots quarter q2 wr ⟨5,by decide⟩]
  decide
#print axioms poly2_wr_5
theorem poly2_wg_0 : polyCoeff quarter q2 wg 0 = (470043520:M) := by
  rw [poly_slots quarter q2 wg ⟨0,by decide⟩]
  decide
#print axioms poly2_wg_0
theorem poly2_wg_1 : polyCoeff quarter q2 wg 1 = (1262748479:M) := by
  rw [poly_slots quarter q2 wg ⟨1,by decide⟩]
  decide
#print axioms poly2_wg_1
theorem poly2_wg_2 : polyCoeff quarter q2 wg 2 = (474337974:M) := by
  rw [poly_slots quarter q2 wg ⟨2,by decide⟩]
  decide
#print axioms poly2_wg_2
theorem poly2_wg_3 : polyCoeff quarter q2 wg 3 = (1453883113:M) := by
  rw [poly_slots quarter q2 wg ⟨3,by decide⟩]
  decide
#print axioms poly2_wg_3
theorem poly2_wg_5 : polyCoeff quarter q2 wg 5 = (1388533620:M) := by
  rw [poly_slots quarter q2 wg ⟨5,by decide⟩]
  decide
#print axioms poly2_wg_5
theorem entry0_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (2:Fin 13) = matrix 0 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot2_1
#print axioms entry0_2
theorem entry1_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (2:Fin 13) = matrix 1 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot2_2
#print axioms entry1_2
theorem entry2_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (2:Fin 13) = matrix 2 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_0
#print axioms entry2_2
theorem entry3_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (2:Fin 13) = matrix 3 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_1
#print axioms entry3_2
theorem entry4_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (2:Fin 13) = matrix 4 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_2
#print axioms entry4_2
theorem entry5_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (2:Fin 13) = matrix 5 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_3
#print axioms entry5_2
theorem entry6_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (2:Fin 13) = matrix 6 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_4
#print axioms entry6_2
theorem entry7_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (2:Fin 13) = matrix 7 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly2_wr_5
#print axioms entry7_2
theorem entry8_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (2:Fin 13) = matrix 8 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly2_wg_0
#print axioms entry8_2
theorem entry9_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (2:Fin 13) = matrix 9 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly2_wg_1
#print axioms entry9_2
theorem entry10_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (2:Fin 13) = matrix 10 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly2_wg_2
#print axioms entry10_2
theorem entry11_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (2:Fin 13) = matrix 11 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly2_wg_3
#print axioms entry11_2
theorem entry12_2 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (2:Fin 13) = matrix 12 2 := by
  simp only [observation, quotient2, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly2_wg_5
#print axioms entry12_2
end
end AspisR19.WitnessEntryData
