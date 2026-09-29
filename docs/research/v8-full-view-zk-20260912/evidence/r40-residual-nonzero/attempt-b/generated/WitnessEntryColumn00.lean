/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient00
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot0_1_0 : (∑ j : Fin 27, q0 ⟨0+j.val,by omega⟩ * WitnessPointData.weights1 ⟨0+j.val,by omega⟩) = (1149050002:M) := by decide
#print axioms dot0_1_0
theorem dot0_1_1 : (∑ j : Fin 27, q0 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (1733763339:M) := by decide
#print axioms dot0_1_1
theorem dot0_1_2 : (∑ j : Fin 27, q0 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (858123418:M) := by decide
#print axioms dot0_1_2
theorem dot0_1_3 : (∑ j : Fin 27, q0 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (2037566159:M) := by decide
#print axioms dot0_1_3
theorem dot0_1 : (∑ r : Fin 108, q0 r * WitnessPointData.weights1 r) = (1483535624:M) := by
  rw [sum108, dot0_1_0, dot0_1_1, dot0_1_2, dot0_1_3]
  decide
#print axioms dot0_1
theorem dot0_2_0 : (∑ j : Fin 27, q0 ⟨0+j.val,by omega⟩ * WitnessPointData.weights2 ⟨0+j.val,by omega⟩) = (1771854000:M) := by decide
#print axioms dot0_2_0
theorem dot0_2_1 : (∑ j : Fin 27, q0 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (526681870:M) := by decide
#print axioms dot0_2_1
theorem dot0_2_2 : (∑ j : Fin 27, q0 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1290885866:M) := by decide
#print axioms dot0_2_2
theorem dot0_2_3 : (∑ j : Fin 27, q0 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (1483905139:M) := by decide
#print axioms dot0_2_3
theorem dot0_2 : (∑ r : Fin 108, q0 r * WitnessPointData.weights2 r) = (778359581:M) := by
  rw [sum108, dot0_2_0, dot0_2_1, dot0_2_2, dot0_2_3]
  decide
#print axioms dot0_2
theorem poly0_wr_0 : polyCoeff quarter q0 wr 0 = (1364832739:M) := by
  rw [poly_slots quarter q0 wr (0:Fin 7)]
  decide
#print axioms poly0_wr_0
theorem poly0_wr_1 : polyCoeff quarter q0 wr 1 = (958692311:M) := by
  rw [poly_slots quarter q0 wr (1:Fin 7)]
  decide
#print axioms poly0_wr_1
theorem poly0_wr_2 : polyCoeff quarter q0 wr 2 = (1696590014:M) := by
  rw [poly_slots quarter q0 wr (2:Fin 7)]
  decide
#print axioms poly0_wr_2
theorem poly0_wr_3 : polyCoeff quarter q0 wr 3 = (1148950004:M) := by
  rw [poly_slots quarter q0 wr (3:Fin 7)]
  decide
#print axioms poly0_wr_3
theorem poly0_wr_4 : polyCoeff quarter q0 wr 4 = (1829981010:M) := by
  rw [poly_slots quarter q0 wr (4:Fin 7)]
  decide
#print axioms poly0_wr_4
theorem poly0_wr_5 : polyCoeff quarter q0 wr 5 = (0:M) := by
  rw [poly_slots quarter q0 wr (5:Fin 7)]
  decide
#print axioms poly0_wr_5
theorem poly0_wg_0 : polyCoeff quarter q0 wg 0 = (1762640600:M) := by
  rw [poly_slots quarter q0 wg (0:Fin 7)]
  decide
#print axioms poly0_wg_0
theorem poly0_wg_1 : polyCoeff quarter q0 wg 1 = (1965274421:M) := by
  rw [poly_slots quarter q0 wg (1:Fin 7)]
  decide
#print axioms poly0_wg_1
theorem poly0_wg_2 : polyCoeff quarter q0 wg 2 = (394173771:M) := by
  rw [poly_slots quarter q0 wg (2:Fin 7)]
  decide
#print axioms poly0_wg_2
theorem poly0_wg_3 : polyCoeff quarter q0 wg 3 = (283862479:M) := by
  rw [poly_slots quarter q0 wg (3:Fin 7)]
  decide
#print axioms poly0_wg_3
theorem poly0_wg_5 : polyCoeff quarter q0 wg 5 = (0:M) := by
  rw [poly_slots quarter q0 wg (5:Fin 7)]
  decide
#print axioms poly0_wg_5
theorem entry0_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (0:Fin 13) = matrix 0 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot0_1
#print axioms entry0_0
theorem entry1_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (0:Fin 13) = matrix 1 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot0_2
#print axioms entry1_0
theorem entry2_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (0:Fin 13) = matrix 2 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_0
#print axioms entry2_0
theorem entry3_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (0:Fin 13) = matrix 3 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_1
#print axioms entry3_0
theorem entry4_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (0:Fin 13) = matrix 4 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_2
#print axioms entry4_0
theorem entry5_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (0:Fin 13) = matrix 5 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_3
#print axioms entry5_0
theorem entry6_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (0:Fin 13) = matrix 6 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_4
#print axioms entry6_0
theorem entry7_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (0:Fin 13) = matrix 7 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly0_wr_5
#print axioms entry7_0
theorem entry8_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (0:Fin 13) = matrix 8 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly0_wg_0
#print axioms entry8_0
theorem entry9_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (0:Fin 13) = matrix 9 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly0_wg_1
#print axioms entry9_0
theorem entry10_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (0:Fin 13) = matrix 10 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly0_wg_2
#print axioms entry10_0
theorem entry11_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (0:Fin 13) = matrix 11 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly0_wg_3
#print axioms entry11_0
theorem entry12_0 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (0:Fin 13) = matrix 12 0 := by
  simp only [observation, quotient0, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly0_wg_5
#print axioms entry12_0
end
end AspisR19.WitnessEntryData
