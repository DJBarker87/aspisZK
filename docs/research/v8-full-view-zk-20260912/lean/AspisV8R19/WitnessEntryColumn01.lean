/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient01
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot1_1_0 : (∑ j : Fin 27, q1 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (1650600263:M) := by decide
#print axioms dot1_1_0
theorem dot1_1_1 : (∑ j : Fin 27, q1 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (293565943:M) := by decide
#print axioms dot1_1_1
theorem dot1_1_2 : (∑ j : Fin 27, q1 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (2038670086:M) := by decide
#print axioms dot1_1_2
theorem dot1_1_3 : (∑ j : Fin 27, q1 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (1657999622:M) := by decide
#print axioms dot1_1_3
theorem dot1_1 : (∑ r : Fin 108, q1 r * WitnessPointData.weights1 r) = (1345868620:M) := by
  rw [sum108, dot1_1_0, dot1_1_1, dot1_1_2, dot1_1_3]
  decide
#print axioms dot1_1
theorem dot1_2_0 : (∑ j : Fin 27, q1 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (985884966:M) := by decide
#print axioms dot1_2_0
theorem dot1_2_1 : (∑ j : Fin 27, q1 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1700552743:M) := by decide
#print axioms dot1_2_1
theorem dot1_2_2 : (∑ j : Fin 27, q1 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (168243095:M) := by decide
#print axioms dot1_2_2
theorem dot1_2_3 : (∑ j : Fin 27, q1 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (1782176028:M) := by decide
#print axioms dot1_2_3
theorem dot1_2 : (∑ r : Fin 108, q1 r * WitnessPointData.weights2 r) = (341889538:M) := by
  rw [sum108, dot1_2_0, dot1_2_1, dot1_2_2, dot1_2_3]
  decide
#print axioms dot1_2
theorem poly1_wr_0 : polyCoeff quarter q1 wr 0 = (963894585:M) := by
  rw [poly_slots quarter q1 wr ⟨0,by decide⟩]
  decide
#print axioms poly1_wr_0
theorem poly1_wr_1 : polyCoeff quarter q1 wr 1 = (1633227975:M) := by
  rw [poly_slots quarter q1 wr ⟨1,by decide⟩]
  decide
#print axioms poly1_wr_1
theorem poly1_wr_2 : polyCoeff quarter q1 wr 2 = (2097404174:M) := by
  rw [poly_slots quarter q1 wr ⟨2,by decide⟩]
  decide
#print axioms poly1_wr_2
theorem poly1_wr_3 : polyCoeff quarter q1 wr 3 = (1149305454:M) := by
  rw [poly_slots quarter q1 wr ⟨3,by decide⟩]
  decide
#print axioms poly1_wr_3
theorem poly1_wr_4 : polyCoeff quarter q1 wr 4 = (1073915192:M) := by
  rw [poly_slots quarter q1 wr ⟨4,by decide⟩]
  decide
#print axioms poly1_wr_4
theorem poly1_wr_5 : polyCoeff quarter q1 wr 5 = (1829981010:M) := by
  rw [poly_slots quarter q1 wr ⟨5,by decide⟩]
  decide
#print axioms poly1_wr_5
theorem poly1_wg_0 : polyCoeff quarter q1 wg 0 = (1601065965:M) := by
  rw [poly_slots quarter q1 wg ⟨0,by decide⟩]
  decide
#print axioms poly1_wg_0
theorem poly1_wg_1 : polyCoeff quarter q1 wg 1 = (487176018:M) := by
  rw [poly_slots quarter q1 wg ⟨1,by decide⟩]
  decide
#print axioms poly1_wg_1
theorem poly1_wg_2 : polyCoeff quarter q1 wg 2 = (429523524:M) := by
  rw [poly_slots quarter q1 wg ⟨2,by decide⟩]
  decide
#print axioms poly1_wg_2
theorem poly1_wg_3 : polyCoeff quarter q1 wg 3 = (233727477:M) := by
  rw [poly_slots quarter q1 wg ⟨3,by decide⟩]
  decide
#print axioms poly1_wg_3
theorem poly1_wg_5 : polyCoeff quarter q1 wg 5 = (157810163:M) := by
  rw [poly_slots quarter q1 wg ⟨5,by decide⟩]
  decide
#print axioms poly1_wg_5
theorem entry0_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (1:Fin 13) = matrix 0 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot1_1
#print axioms entry0_1
theorem entry1_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (1:Fin 13) = matrix 1 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot1_2
#print axioms entry1_1
theorem entry2_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (1:Fin 13) = matrix 2 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_0
#print axioms entry2_1
theorem entry3_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (1:Fin 13) = matrix 3 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_1
#print axioms entry3_1
theorem entry4_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (1:Fin 13) = matrix 4 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_2
#print axioms entry4_1
theorem entry5_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (1:Fin 13) = matrix 5 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_3
#print axioms entry5_1
theorem entry6_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (1:Fin 13) = matrix 6 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_4
#print axioms entry6_1
theorem entry7_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (1:Fin 13) = matrix 7 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly1_wr_5
#print axioms entry7_1
theorem entry8_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (1:Fin 13) = matrix 8 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly1_wg_0
#print axioms entry8_1
theorem entry9_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (1:Fin 13) = matrix 9 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly1_wg_1
#print axioms entry9_1
theorem entry10_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (1:Fin 13) = matrix 10 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly1_wg_2
#print axioms entry10_1
theorem entry11_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (1:Fin 13) = matrix 11 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly1_wg_3
#print axioms entry11_1
theorem entry12_1 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (1:Fin 13) = matrix 12 1 := by
  simp only [observation, quotient1, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly1_wg_5
#print axioms entry12_1
end
end AspisR19.WitnessEntryData
