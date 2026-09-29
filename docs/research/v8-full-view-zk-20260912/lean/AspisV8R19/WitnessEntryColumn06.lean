/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient06
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot6_1_0 : (∑ j : Fin 27, q6 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (1848912178:M) := by decide
#print axioms dot6_1_0
theorem dot6_1_1 : (∑ j : Fin 27, q6 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (283742548:M) := by decide
#print axioms dot6_1_1
theorem dot6_1_2 : (∑ j : Fin 27, q6 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (1622129946:M) := by decide
#print axioms dot6_1_2
theorem dot6_1_3 : (∑ j : Fin 27, q6 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1735302673:M) := by decide
#print axioms dot6_1_3
theorem dot6_1 : (∑ r : Fin 108, q6 r * WitnessPointData.weights1 r) = (1195120051:M) := by
  rw [sum108, dot6_1_0, dot6_1_1, dot6_1_2, dot6_1_3]
  decide
#print axioms dot6_1
theorem dot6_2_0 : (∑ j : Fin 27, q6 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (258938213:M) := by decide
#print axioms dot6_2_0
theorem dot6_2_1 : (∑ j : Fin 27, q6 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (820180636:M) := by decide
#print axioms dot6_2_1
theorem dot6_2_2 : (∑ j : Fin 27, q6 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (2008583912:M) := by decide
#print axioms dot6_2_2
theorem dot6_2_3 : (∑ j : Fin 27, q6 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (840304467:M) := by decide
#print axioms dot6_2_3
theorem dot6_2 : (∑ r : Fin 108, q6 r * WitnessPointData.weights2 r) = (1780523581:M) := by
  rw [sum108, dot6_2_0, dot6_2_1, dot6_2_2, dot6_2_3]
  decide
#print axioms dot6_2
theorem poly6_wr_0 : polyCoeff quarter q6 wr 0 = (1465345841:M) := by
  rw [poly_slots quarter q6 wr ⟨0,by decide⟩]
  decide
#print axioms poly6_wr_0
theorem poly6_wr_1 : polyCoeff quarter q6 wr 1 = (150623050:M) := by
  rw [poly_slots quarter q6 wr ⟨1,by decide⟩]
  decide
#print axioms poly6_wr_1
theorem poly6_wr_2 : polyCoeff quarter q6 wr 2 = (533455839:M) := by
  rw [poly_slots quarter q6 wr ⟨2,by decide⟩]
  decide
#print axioms poly6_wr_2
theorem poly6_wr_3 : polyCoeff quarter q6 wr 3 = (1154120950:M) := by
  rw [poly_slots quarter q6 wr ⟨3,by decide⟩]
  decide
#print axioms poly6_wr_3
theorem poly6_wr_4 : polyCoeff quarter q6 wr 4 = (1570870686:M) := by
  rw [poly_slots quarter q6 wr ⟨4,by decide⟩]
  decide
#print axioms poly6_wr_4
theorem poly6_wr_5 : polyCoeff quarter q6 wr 5 = (0:M) := by
  rw [poly_slots quarter q6 wr ⟨5,by decide⟩]
  decide
#print axioms poly6_wr_5
theorem poly6_wg_0 : polyCoeff quarter q6 wg 0 = (1399310780:M) := by
  rw [poly_slots quarter q6 wg ⟨0,by decide⟩]
  decide
#print axioms poly6_wg_0
theorem poly6_wg_1 : polyCoeff quarter q6 wg 1 = (2128520806:M) := by
  rw [poly_slots quarter q6 wg ⟨1,by decide⟩]
  decide
#print axioms poly6_wg_1
theorem poly6_wg_2 : polyCoeff quarter q6 wg 2 = (575714444:M) := by
  rw [poly_slots quarter q6 wg ⟨2,by decide⟩]
  decide
#print axioms poly6_wg_2
theorem poly6_wg_3 : polyCoeff quarter q6 wg 3 = (979853685:M) := by
  rw [poly_slots quarter q6 wg ⟨3,by decide⟩]
  decide
#print axioms poly6_wg_3
theorem poly6_wg_5 : polyCoeff quarter q6 wg 5 = (0:M) := by
  rw [poly_slots quarter q6 wg ⟨5,by decide⟩]
  decide
#print axioms poly6_wg_5
theorem entry0_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (6:Fin 13) = matrix 0 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot6_1
#print axioms entry0_6
theorem entry1_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (6:Fin 13) = matrix 1 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot6_2
#print axioms entry1_6
theorem entry2_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (6:Fin 13) = matrix 2 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_0
#print axioms entry2_6
theorem entry3_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (6:Fin 13) = matrix 3 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_1
#print axioms entry3_6
theorem entry4_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (6:Fin 13) = matrix 4 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_2
#print axioms entry4_6
theorem entry5_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (6:Fin 13) = matrix 5 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_3
#print axioms entry5_6
theorem entry6_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (6:Fin 13) = matrix 6 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_4
#print axioms entry6_6
theorem entry7_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (6:Fin 13) = matrix 7 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly6_wr_5
#print axioms entry7_6
theorem entry8_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (6:Fin 13) = matrix 8 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly6_wg_0
#print axioms entry8_6
theorem entry9_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (6:Fin 13) = matrix 9 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly6_wg_1
#print axioms entry9_6
theorem entry10_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (6:Fin 13) = matrix 10 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly6_wg_2
#print axioms entry10_6
theorem entry11_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (6:Fin 13) = matrix 11 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly6_wg_3
#print axioms entry11_6
theorem entry12_6 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (6:Fin 13) = matrix 12 6 := by
  simp only [observation, quotient6, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly6_wg_5
#print axioms entry12_6
end
end AspisR19.WitnessEntryData
