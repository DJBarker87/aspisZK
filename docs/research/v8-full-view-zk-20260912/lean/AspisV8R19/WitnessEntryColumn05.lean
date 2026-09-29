/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient05
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot5_1_0 : (∑ j : Fin 27, q5 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (195222377:M) := by decide
#print axioms dot5_1_0
theorem dot5_1_1 : (∑ j : Fin 27, q5 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (837215596:M) := by decide
#print axioms dot5_1_1
theorem dot5_1_2 : (∑ j : Fin 27, q5 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (658840740:M) := by decide
#print axioms dot5_1_2
theorem dot5_1_3 : (∑ j : Fin 27, q5 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1137453064:M) := by decide
#print axioms dot5_1_3
theorem dot5_1 : (∑ r : Fin 108, q5 r * WitnessPointData.weights1 r) = (681248130:M) := by
  rw [sum108, dot5_1_0, dot5_1_1, dot5_1_2, dot5_1_3]
  decide
#print axioms dot5_1
theorem dot5_2_0 : (∑ j : Fin 27, q5 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1759959929:M) := by decide
#print axioms dot5_2_0
theorem dot5_2_1 : (∑ j : Fin 27, q5 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1548966392:M) := by decide
#print axioms dot5_2_1
theorem dot5_2_2 : (∑ j : Fin 27, q5 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (329544355:M) := by decide
#print axioms dot5_2_2
theorem dot5_2_3 : (∑ j : Fin 27, q5 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (865687566:M) := by decide
#print axioms dot5_2_3
theorem dot5_2 : (∑ r : Fin 108, q5 r * WitnessPointData.weights2 r) = (209190948:M) := by
  rw [sum108, dot5_2_0, dot5_2_1, dot5_2_2, dot5_2_3]
  decide
#print axioms dot5_2
theorem poly5_wr_0 : polyCoeff quarter q5 wr 0 = (779580779:M) := by
  rw [poly_slots quarter q5 wr ⟨0,by decide⟩]
  decide
#print axioms poly5_wr_0
theorem poly5_wr_1 : polyCoeff quarter q5 wr 1 = (1182069878:M) := by
  rw [poly_slots quarter q5 wr ⟨1,by decide⟩]
  decide
#print axioms poly5_wr_1
theorem poly5_wr_2 : polyCoeff quarter q5 wr 2 = (1344070501:M) := by
  rw [poly_slots quarter q5 wr ⟨2,by decide⟩]
  decide
#print axioms poly5_wr_2
theorem poly5_wr_3 : polyCoeff quarter q5 wr 3 = (538005895:M) := by
  rw [poly_slots quarter q5 wr ⟨3,by decide⟩]
  decide
#print axioms poly5_wr_3
theorem poly5_wr_4 : polyCoeff quarter q5 wr 4 = (1067165113:M) := by
  rw [poly_slots quarter q5 wr ⟨4,by decide⟩]
  decide
#print axioms poly5_wr_4
theorem poly5_wr_5 : polyCoeff quarter q5 wr 5 = (1160606087:M) := by
  rw [poly_slots quarter q5 wr ⟨5,by decide⟩]
  decide
#print axioms poly5_wr_5
theorem poly5_wg_0 : polyCoeff quarter q5 wg 0 = (914883790:M) := by
  rw [poly_slots quarter q5 wg ⟨0,by decide⟩]
  decide
#print axioms poly5_wg_0
theorem poly5_wg_1 : polyCoeff quarter q5 wg 1 = (916924197:M) := by
  rw [poly_slots quarter q5 wg ⟨1,by decide⟩]
  decide
#print axioms poly5_wg_1
theorem poly5_wg_2 : polyCoeff quarter q5 wg 2 = (949676945:M) := by
  rw [poly_slots quarter q5 wg ⟨2,by decide⟩]
  decide
#print axioms poly5_wg_2
theorem poly5_wg_3 : polyCoeff quarter q5 wg 3 = (1285229135:M) := by
  rw [poly_slots quarter q5 wg ⟨3,by decide⟩]
  decide
#print axioms poly5_wg_3
theorem poly5_wg_5 : polyCoeff quarter q5 wg 5 = (1268190972:M) := by
  rw [poly_slots quarter q5 wg ⟨5,by decide⟩]
  decide
#print axioms poly5_wg_5
theorem entry0_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (5:Fin 13) = matrix 0 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot5_1
#print axioms entry0_5
theorem entry1_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (5:Fin 13) = matrix 1 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot5_2
#print axioms entry1_5
theorem entry2_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (5:Fin 13) = matrix 2 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_0
#print axioms entry2_5
theorem entry3_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (5:Fin 13) = matrix 3 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_1
#print axioms entry3_5
theorem entry4_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (5:Fin 13) = matrix 4 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_2
#print axioms entry4_5
theorem entry5_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (5:Fin 13) = matrix 5 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_3
#print axioms entry5_5
theorem entry6_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (5:Fin 13) = matrix 6 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_4
#print axioms entry6_5
theorem entry7_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (5:Fin 13) = matrix 7 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly5_wr_5
#print axioms entry7_5
theorem entry8_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (5:Fin 13) = matrix 8 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly5_wg_0
#print axioms entry8_5
theorem entry9_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (5:Fin 13) = matrix 9 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly5_wg_1
#print axioms entry9_5
theorem entry10_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (5:Fin 13) = matrix 10 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly5_wg_2
#print axioms entry10_5
theorem entry11_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (5:Fin 13) = matrix 11 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly5_wg_3
#print axioms entry11_5
theorem entry12_5 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (5:Fin 13) = matrix 12 5 := by
  simp only [observation, quotient5, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly5_wg_5
#print axioms entry12_5
end
end AspisR19.WitnessEntryData
