/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient08
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot8_1_0 : (∑ j : Fin 27, q8 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (980899385:M) := by decide
#print axioms dot8_1_0
theorem dot8_1_1 : (∑ j : Fin 27, q8 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (1249868774:M) := by decide
#print axioms dot8_1_1
theorem dot8_1_2 : (∑ j : Fin 27, q8 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (2069672770:M) := by decide
#print axioms dot8_1_2
theorem dot8_1_3 : (∑ j : Fin 27, q8 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1939999212:M) := by decide
#print axioms dot8_1_3
theorem dot8_1 : (∑ r : Fin 108, q8 r * WitnessPointData.weights1 r) = (1945472847:M) := by
  rw [sum108, dot8_1_0, dot8_1_1, dot8_1_2, dot8_1_3]
  decide
#print axioms dot8_1
theorem dot8_2_0 : (∑ j : Fin 27, q8 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (1362200123:M) := by decide
#print axioms dot8_2_0
theorem dot8_2_1 : (∑ j : Fin 27, q8 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (147273729:M) := by decide
#print axioms dot8_2_1
theorem dot8_2_2 : (∑ j : Fin 27, q8 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1513134079:M) := by decide
#print axioms dot8_2_2
theorem dot8_2_3 : (∑ j : Fin 27, q8 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (899622097:M) := by decide
#print axioms dot8_2_3
theorem dot8_2 : (∑ r : Fin 108, q8 r * WitnessPointData.weights2 r) = (1774746381:M) := by
  rw [sum108, dot8_2_0, dot8_2_1, dot8_2_2, dot8_2_3]
  decide
#print axioms dot8_2
theorem poly8_wr_0 : polyCoeff quarter q8 wr 0 = (934985858:M) := by
  rw [poly_slots quarter q8 wr ⟨0,by decide⟩]
  decide
#print axioms poly8_wr_0
theorem poly8_wr_1 : polyCoeff quarter q8 wr 1 = (458081161:M) := by
  rw [poly_slots quarter q8 wr ⟨1,by decide⟩]
  decide
#print axioms poly8_wr_1
theorem poly8_wr_2 : polyCoeff quarter q8 wr 2 = (741755891:M) := by
  rw [poly_slots quarter q8 wr ⟨2,by decide⟩]
  decide
#print axioms poly8_wr_2
theorem poly8_wr_3 : polyCoeff quarter q8 wr 3 = (307198357:M) := by
  rw [poly_slots quarter q8 wr ⟨3,by decide⟩]
  decide
#print axioms poly8_wr_3
theorem poly8_wr_4 : polyCoeff quarter q8 wr 4 = (1833103870:M) := by
  rw [poly_slots quarter q8 wr ⟨4,by decide⟩]
  decide
#print axioms poly8_wr_4
theorem poly8_wr_5 : polyCoeff quarter q8 wr 5 = (1412797517:M) := by
  rw [poly_slots quarter q8 wr ⟨5,by decide⟩]
  decide
#print axioms poly8_wr_5
theorem poly8_wg_0 : polyCoeff quarter q8 wg 0 = (1994235163:M) := by
  rw [poly_slots quarter q8 wg ⟨0,by decide⟩]
  decide
#print axioms poly8_wg_0
theorem poly8_wg_1 : polyCoeff quarter q8 wg 1 = (276061663:M) := by
  rw [poly_slots quarter q8 wg ⟨1,by decide⟩]
  decide
#print axioms poly8_wg_1
theorem poly8_wg_2 : polyCoeff quarter q8 wg 2 = (1559291238:M) := by
  rw [poly_slots quarter q8 wg ⟨2,by decide⟩]
  decide
#print axioms poly8_wg_2
theorem poly8_wg_3 : polyCoeff quarter q8 wg 3 = (484261304:M) := by
  rw [poly_slots quarter q8 wg ⟨3,by decide⟩]
  decide
#print axioms poly8_wg_3
theorem poly8_wg_5 : polyCoeff quarter q8 wg 5 = (1316500753:M) := by
  rw [poly_slots quarter q8 wg ⟨5,by decide⟩]
  decide
#print axioms poly8_wg_5
theorem entry0_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (8:Fin 13) = matrix 0 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot8_1
#print axioms entry0_8
theorem entry1_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (8:Fin 13) = matrix 1 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot8_2
#print axioms entry1_8
theorem entry2_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (8:Fin 13) = matrix 2 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_0
#print axioms entry2_8
theorem entry3_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (8:Fin 13) = matrix 3 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_1
#print axioms entry3_8
theorem entry4_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (8:Fin 13) = matrix 4 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_2
#print axioms entry4_8
theorem entry5_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (8:Fin 13) = matrix 5 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_3
#print axioms entry5_8
theorem entry6_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (8:Fin 13) = matrix 6 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_4
#print axioms entry6_8
theorem entry7_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (8:Fin 13) = matrix 7 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly8_wr_5
#print axioms entry7_8
theorem entry8_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (8:Fin 13) = matrix 8 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly8_wg_0
#print axioms entry8_8
theorem entry9_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (8:Fin 13) = matrix 9 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly8_wg_1
#print axioms entry9_8
theorem entry10_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (8:Fin 13) = matrix 10 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly8_wg_2
#print axioms entry10_8
theorem entry11_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (8:Fin 13) = matrix 11 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly8_wg_3
#print axioms entry11_8
theorem entry12_8 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (8:Fin 13) = matrix 12 8 := by
  simp only [observation, quotient8, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly8_wg_5
#print axioms entry12_8
end
end AspisR19.WitnessEntryData
