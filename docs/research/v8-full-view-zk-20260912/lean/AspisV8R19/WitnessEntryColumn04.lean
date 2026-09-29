/- Generated staged residual-entry certificate. -/
import AspisV8R19.WitnessQuotient04
namespace AspisR19.WitnessEntryData
open RootCertificate ResidualModel ResidualEntryCertificate
noncomputable section
theorem dot4_1_0 : (∑ j : Fin 27, q4 ⟨j.val,by omega⟩ * WitnessPointData.weights1 ⟨j.val,by omega⟩) = (913568963:M) := by decide
#print axioms dot4_1_0
theorem dot4_1_1 : (∑ j : Fin 27, q4 ⟨27+j.val,by omega⟩ * WitnessPointData.weights1 ⟨27+j.val,by omega⟩) = (220589967:M) := by decide
#print axioms dot4_1_1
theorem dot4_1_2 : (∑ j : Fin 27, q4 ⟨54+j.val,by omega⟩ * WitnessPointData.weights1 ⟨54+j.val,by omega⟩) = (914762772:M) := by decide
#print axioms dot4_1_2
theorem dot4_1_3 : (∑ j : Fin 27, q4 ⟨81+j.val,by omega⟩ * WitnessPointData.weights1 ⟨81+j.val,by omega⟩) = (583137537:M) := by decide
#print axioms dot4_1_3
theorem dot4_1 : (∑ r : Fin 108, q4 r * WitnessPointData.weights1 r) = (484575592:M) := by
  rw [sum108, dot4_1_0, dot4_1_1, dot4_1_2, dot4_1_3]
  decide
#print axioms dot4_1
theorem dot4_2_0 : (∑ j : Fin 27, q4 ⟨j.val,by omega⟩ * WitnessPointData.weights2 ⟨j.val,by omega⟩) = (271779595:M) := by decide
#print axioms dot4_2_0
theorem dot4_2_1 : (∑ j : Fin 27, q4 ⟨27+j.val,by omega⟩ * WitnessPointData.weights2 ⟨27+j.val,by omega⟩) = (1341019966:M) := by decide
#print axioms dot4_2_1
theorem dot4_2_2 : (∑ j : Fin 27, q4 ⟨54+j.val,by omega⟩ * WitnessPointData.weights2 ⟨54+j.val,by omega⟩) = (1485777321:M) := by decide
#print axioms dot4_2_2
theorem dot4_2_3 : (∑ j : Fin 27, q4 ⟨81+j.val,by omega⟩ * WitnessPointData.weights2 ⟨81+j.val,by omega⟩) = (695108865:M) := by decide
#print axioms dot4_2_3
theorem dot4_2 : (∑ r : Fin 108, q4 r * WitnessPointData.weights2 r) = (1646202100:M) := by
  rw [sum108, dot4_2_0, dot4_2_1, dot4_2_2, dot4_2_3]
  decide
#print axioms dot4_2
theorem poly4_wr_0 : polyCoeff quarter q4 wr 0 = (724935439:M) := by
  rw [poly_slots quarter q4 wr ⟨0,by decide⟩]
  decide
#print axioms poly4_wr_0
theorem poly4_wr_1 : polyCoeff quarter q4 wr 1 = (1396000638:M) := by
  rw [poly_slots quarter q4 wr ⟨1,by decide⟩]
  decide
#print axioms poly4_wr_1
theorem poly4_wr_2 : polyCoeff quarter q4 wr 2 = (1886437149:M) := by
  rw [poly_slots quarter q4 wr ⟨2,by decide⟩]
  decide
#print axioms poly4_wr_2
theorem poly4_wr_3 : polyCoeff quarter q4 wr 3 = (1953790812:M) := by
  rw [poly_slots quarter q4 wr ⟨3,by decide⟩]
  decide
#print axioms poly4_wr_3
theorem poly4_wr_4 : polyCoeff quarter q4 wr 4 = (1160606087:M) := by
  rw [poly_slots quarter q4 wr ⟨4,by decide⟩]
  decide
#print axioms poly4_wr_4
theorem poly4_wr_5 : polyCoeff quarter q4 wr 5 = (332515173:M) := by
  rw [poly_slots quarter q4 wr ⟨5,by decide⟩]
  decide
#print axioms poly4_wr_5
theorem poly4_wg_0 : polyCoeff quarter q4 wg 0 = (1664614575:M) := by
  rw [poly_slots quarter q4 wg ⟨0,by decide⟩]
  decide
#print axioms poly4_wg_0
theorem poly4_wg_1 : polyCoeff quarter q4 wg 1 = (130989171:M) := by
  rw [poly_slots quarter q4 wg ⟨1,by decide⟩]
  decide
#print axioms poly4_wg_1
theorem poly4_wg_2 : polyCoeff quarter q4 wg 2 = (452305984:M) := by
  rw [poly_slots quarter q4 wg ⟨2,by decide⟩]
  decide
#print axioms poly4_wg_2
theorem poly4_wg_3 : polyCoeff quarter q4 wg 3 = (968394676:M) := by
  rw [poly_slots quarter q4 wg ⟨3,by decide⟩]
  decide
#print axioms poly4_wg_3
theorem poly4_wg_5 : polyCoeff quarter q4 wg 5 = (1474745042:M) := by
  rw [poly_slots quarter q4 wg ⟨5,by decide⟩]
  decide
#print axioms poly4_wg_5
theorem entry0_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 1 (4:Fin 13) = matrix 0 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot4_1
#print axioms entry0_4
theorem entry1_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 2 (4:Fin 13) = matrix 1 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  exact dot4_2
#print axioms entry1_4
theorem entry2_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 3 (4:Fin 13) = matrix 2 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_0
#print axioms entry2_4
theorem entry3_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 4 (4:Fin 13) = matrix 3 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_1
#print axioms entry3_4
theorem entry4_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 5 (4:Fin 13) = matrix 4 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_2
#print axioms entry4_4
theorem entry5_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 6 (4:Fin 13) = matrix 5 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_3
#print axioms entry5_4
theorem entry6_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 7 (4:Fin 13) = matrix 6 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_4
#print axioms entry6_4
theorem entry7_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 8 (4:Fin 13) = matrix 7 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wr_stage]
  exact poly4_wr_5
#print axioms entry7_4
theorem entry8_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 10 (4:Fin 13) = matrix 8 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly4_wg_0
#print axioms entry8_4
theorem entry9_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 11 (4:Fin 13) = matrix 9 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly4_wg_1
#print axioms entry9_4
theorem entry10_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 12 (4:Fin 13) = matrix 10 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly4_wg_2
#print axioms entry10_4
theorem entry11_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 13 (4:Fin 13) = matrix 11 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly4_wg_3
#print axioms entry11_4
theorem entry12_4 : observation ResidualPins.order ResidualPins.inactive half quarter (7:M) 5 (-5) 5 7 WitnessPointData.z (SourceResidualPolynomial.rootCoefficients half WitnessRootData.roots) 15 (4:Fin 13) = matrix 12 4 := by
  simp only [observation, quotient4, Nat.reduceEqDiff, Nat.reduceLT, ite_false, ite_true, Nat.reduceSub, WitnessPointData.point_weight0, WitnessPointData.point_weight1, WitnessPointData.point_weight2]
  rw [wg_stage]
  exact poly4_wg_5
#print axioms entry12_4
end
end AspisR19.WitnessEntryData
