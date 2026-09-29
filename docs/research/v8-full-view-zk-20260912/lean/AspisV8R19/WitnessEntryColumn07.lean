/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient07
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot7_1_0 : (∑ j : Fin 27, q7 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (1376794044:M) := by decide
#print axioms dot7_1_0
theorem dot7_1_1 : (∑ j : Fin 27, q7 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (1554659587:M) := by decide
#print axioms dot7_1_1
theorem dot7_1_2 : (∑ j : Fin 27, q7 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1565336658:M) := by decide
#print axioms dot7_1_2
theorem dot7_1_3 : (∑ j : Fin 27, q7 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (70496712:M) := by decide
#print axioms dot7_1_3
theorem dot7_1 : (∑ r : Fin 108, q7 r * WitnessPointData.weights1 r) = (272319707:M) := by
  rw [sum108, dot7_1_0, dot7_1_1, dot7_1_2, dot7_1_3]
  decide
#print axioms dot7_1
theorem dot7_2_0 : (∑ j : Fin 27, q7 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (176872902:M) := by decide
#print axioms dot7_2_0
theorem dot7_2_1 : (∑ j : Fin 27, q7 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (406860639:M) := by decide
#print axioms dot7_2_1
theorem dot7_2_2 : (∑ j : Fin 27, q7 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1760914139:M) := by decide
#print axioms dot7_2_2
theorem dot7_2_3 : (∑ j : Fin 27, q7 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (258564487:M) := by decide
#print axioms dot7_2_3
theorem dot7_2 : (∑ r : Fin 108, q7 r * WitnessPointData.weights2 r) = (455728520:M) := by
  rw [sum108, dot7_2_0, dot7_2_1, dot7_2_2, dot7_2_3]
  decide
#print axioms dot7_2
theorem poly7_wr_0 : polyCoeff quarter q7 wr 0 = (1667486299:M) := by
  rw [poly_slots quarter q7 wr ⟨0,by decide⟩]
  decide
#print axioms poly7_wr_0
theorem poly7_wr_1 : polyCoeff quarter q7 wr 1 = (372223544:M) := by
  rw [poly_slots quarter q7 wr ⟨1,by decide⟩]
  decide
#print axioms poly7_wr_1
theorem poly7_wr_2 : polyCoeff quarter q7 wr 2 = (1737330276:M) := by
  rw [poly_slots quarter q7 wr ⟨2,by decide⟩]
  decide
#print axioms poly7_wr_2
theorem poly7_wr_3 : polyCoeff quarter q7 wr 3 = (22367901:M) := by
  rw [poly_slots quarter q7 wr ⟨3,by decide⟩]
  decide
#print axioms poly7_wr_3
theorem poly7_wr_4 : polyCoeff quarter q7 wr 4 = (1412797517:M) := by
  rw [poly_slots quarter q7 wr ⟨4,by decide⟩]
  decide
#print axioms poly7_wr_4
theorem poly7_wr_5 : polyCoeff quarter q7 wr 5 = (1570870686:M) := by
  rw [poly_slots quarter q7 wr ⟨5,by decide⟩]
  decide
#print axioms poly7_wr_5
theorem poly7_wg_0 : polyCoeff quarter q7 wg 0 = (1205240872:M) := by
  rw [poly_slots quarter q7 wg ⟨0,by decide⟩]
  decide
#print axioms poly7_wg_0
theorem poly7_wg_1 : polyCoeff quarter q7 wg 1 = (1266570893:M) := by
  rw [poly_slots quarter q7 wg ⟨1,by decide⟩]
  decide
#print axioms poly7_wg_1
theorem poly7_wg_2 : polyCoeff quarter q7 wg 2 = (1863554620:M) := by
  rw [poly_slots quarter q7 wg ⟨2,by decide⟩]
  decide
#print axioms poly7_wg_2
theorem poly7_wg_3 : polyCoeff quarter q7 wg 3 = (992239298:M) := by
  rw [poly_slots quarter q7 wg ⟨3,by decide⟩]
  decide
#print axioms poly7_wg_3
theorem poly7_wg_5 : polyCoeff quarter q7 wg 5 = (1582009329:M) := by
  rw [poly_slots quarter q7 wg ⟨5,by decide⟩]
  decide
#print axioms poly7_wg_5
theorem entry0_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (7:Fin 13) = matrix 0 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot7_1
#print axioms entry0_7
theorem entry1_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (7:Fin 13) = matrix 1 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot7_2
#print axioms entry1_7
theorem entry2_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (7:Fin 13) = matrix 2 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_0
#print axioms entry2_7
theorem entry3_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (7:Fin 13) = matrix 3 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_1
#print axioms entry3_7
theorem entry4_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (7:Fin 13) = matrix 4 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_2
#print axioms entry4_7
theorem entry5_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (7:Fin 13) = matrix 5 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_3
#print axioms entry5_7
theorem entry6_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (7:Fin 13) = matrix 6 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_4
#print axioms entry6_7
theorem entry7_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (7:Fin 13) = matrix 7 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly7_wr_5
#print axioms entry7_7
theorem entry8_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (7:Fin 13) = matrix 8 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly7_wg_0
#print axioms entry8_7
theorem entry9_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (7:Fin 13) = matrix 9 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly7_wg_1
#print axioms entry9_7
theorem entry10_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (7:Fin 13) = matrix 10 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly7_wg_2
#print axioms entry10_7
theorem entry11_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (7:Fin 13) = matrix 11 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly7_wg_3
#print axioms entry11_7
theorem entry12_7 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (7:Fin 13) = matrix 12 7 := by
  simp only [observation, quotient7, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly7_wg_5
#print axioms entry12_7
end
end AspisR19.WitnessEntryData
