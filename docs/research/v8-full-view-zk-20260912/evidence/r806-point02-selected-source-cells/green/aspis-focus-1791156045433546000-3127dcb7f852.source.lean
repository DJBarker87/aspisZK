import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk12P0
import AspisV8R19.R780Point02WeightChunk12P2
import AspisV8R19.R780Point02WeightChunk13P0
import AspisV8R19.R780Point02WeightChunk13P2
import AspisV8R19.R780Point02WeightChunk14P0
import AspisV8R19.R780Point02WeightChunk14P2
import AspisV8R19.R780Point02WeightChunk15P0
import AspisV8R19.R780Point02WeightChunk15P2
import AspisV8R19.R780Point02WeightChunk16P0
import AspisV8R19.R780Point02WeightChunk16P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk12P0
open AspisV8R19.R780Point02WeightChunk12P2
open AspisV8R19.R780Point02WeightChunk13P0
open AspisV8R19.R780Point02WeightChunk13P2
open AspisV8R19.R780Point02WeightChunk14P0
open AspisV8R19.R780Point02WeightChunk14P2
open AspisV8R19.R780Point02WeightChunk15P0
open AspisV8R19.R780Point02WeightChunk15P2
open AspisV8R19.R780Point02WeightChunk16P0
open AspisV8R19.R780Point02WeightChunk16P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk01
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 32, flat 8. -/
theorem p0_d044_s1_flat08 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 178 - 7^(1+1)*pw0 176) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0178, pw0_0176, pw0_0002, pw0_0000]
  decide
#print axioms p0_d044_s1_flat08
/-- Pinned raw matrix row 216, raw column 32, flat 8. -/
theorem p2_d044_s1_flat08 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 178 - 7^(1+1)*pw2 176) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0178, pw2_0176, pw2_0002, pw2_0000]
  decide
#print axioms p2_d044_s1_flat08
/-- Pinned raw matrix row 214, raw column 33, flat 9. -/
theorem p0_d045_s0_flat09 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 45 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 181 - 7^(0+1)*pw0 180) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0181, pw0_0180, pw0_0001, pw0_0000]
  decide
#print axioms p0_d045_s0_flat09
/-- Pinned raw matrix row 216, raw column 33, flat 9. -/
theorem p2_d045_s0_flat09 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 45 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 181 - 7^(0+1)*pw2 180) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0181, pw2_0180, pw2_0001, pw2_0000]
  decide
#print axioms p2_d045_s0_flat09
/-- Pinned raw matrix row 214, raw column 23, flat 10. -/
theorem p0_d040_s0_flat10 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 161 - 7^(0+1)*pw0 160) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0161, pw0_0160, pw0_0001, pw0_0000]
  decide
#print axioms p0_d040_s0_flat10
/-- Pinned raw matrix row 216, raw column 23, flat 10. -/
theorem p2_d040_s0_flat10 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 161 - 7^(0+1)*pw2 160) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0161, pw2_0160, pw2_0001, pw2_0000]
  decide
#print axioms p2_d040_s0_flat10
/-- Pinned raw matrix row 214, raw column 24, flat 11. -/
theorem p0_d040_s1_flat11 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 162 - 7^(1+1)*pw0 160) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0162, pw0_0160, pw0_0002, pw0_0000]
  decide
#print axioms p0_d040_s1_flat11
/-- Pinned raw matrix row 216, raw column 24, flat 11. -/
theorem p2_d040_s1_flat11 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 40 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 162 - 7^(1+1)*pw2 160) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0162, pw2_0160, pw2_0002, pw2_0000]
  decide
#print axioms p2_d040_s1_flat11
/-- Pinned raw matrix row 214, raw column 25, flat 12. -/
theorem p0_d041_s0_flat12 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 165 - 7^(0+1)*pw0 164) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0165, pw0_0164, pw0_0001, pw0_0000]
  decide
#print axioms p0_d041_s0_flat12
/-- Pinned raw matrix row 216, raw column 25, flat 12. -/
theorem p2_d041_s0_flat12 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 165 - 7^(0+1)*pw2 164) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0165, pw2_0164, pw2_0001, pw2_0000]
  decide
#print axioms p2_d041_s0_flat12
/-- Pinned raw matrix row 214, raw column 26, flat 13. -/
theorem p0_d041_s1_flat13 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 166 - 7^(1+1)*pw0 164) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0166, pw0_0164, pw0_0002, pw0_0000]
  decide
#print axioms p0_d041_s1_flat13
/-- Pinned raw matrix row 216, raw column 26, flat 13. -/
theorem p2_d041_s1_flat13 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 41 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 166 - 7^(1+1)*pw2 164) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0166, pw2_0164, pw2_0002, pw2_0000]
  decide
#print axioms p2_d041_s1_flat13
/-- Pinned raw matrix row 214, raw column 27, flat 14. -/
theorem p0_d042_s0_flat14 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 169 - 7^(0+1)*pw0 168) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0169, pw0_0168, pw0_0001, pw0_0000]
  decide
#print axioms p0_d042_s0_flat14
/-- Pinned raw matrix row 216, raw column 27, flat 14. -/
theorem p2_d042_s0_flat14 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 169 - 7^(0+1)*pw2 168) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0169, pw2_0168, pw2_0001, pw2_0000]
  decide
#print axioms p2_d042_s0_flat14
/-- Pinned raw matrix row 214, raw column 28, flat 15. -/
theorem p0_d042_s1_flat15 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 170 - 7^(1+1)*pw0 168) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0170, pw0_0168, pw0_0002, pw0_0000]
  decide
#print axioms p0_d042_s1_flat15
/-- Pinned raw matrix row 216, raw column 28, flat 15. -/
theorem p2_d042_s1_flat15 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 42 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 170 - 7^(1+1)*pw2 168) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0170, pw2_0168, pw2_0002, pw2_0000]
  decide
#print axioms p2_d042_s1_flat15
end AspisV8R19.R806Point02SelectedChunk01
