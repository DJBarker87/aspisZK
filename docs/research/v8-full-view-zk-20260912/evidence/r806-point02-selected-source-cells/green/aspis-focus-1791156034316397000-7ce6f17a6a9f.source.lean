import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk01P0
import AspisV8R19.R780Point02WeightChunk01P2
import AspisV8R19.R780Point02WeightChunk02P0
import AspisV8R19.R780Point02WeightChunk02P2
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
open AspisV8R19.R780Point02WeightChunk01P0
open AspisV8R19.R780Point02WeightChunk01P2
open AspisV8R19.R780Point02WeightChunk02P0
open AspisV8R19.R780Point02WeightChunk02P2
open AspisV8R19.R780Point02WeightChunk15P0
open AspisV8R19.R780Point02WeightChunk15P2
open AspisV8R19.R780Point02WeightChunk16P0
open AspisV8R19.R780Point02WeightChunk16P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk00
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 214, flat 0. -/
theorem p0_d023_s0_flat00 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 93 - 7^(0+1)*pw0 92) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0093, pw0_0092, pw0_0001, pw0_0000]
  decide
#print axioms p0_d023_s0_flat00
/-- Pinned raw matrix row 216, raw column 214, flat 0. -/
theorem p2_d023_s0_flat00 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 93 - 7^(0+1)*pw2 92) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0093, pw2_0092, pw2_0001, pw2_0000]
  decide
#print axioms p2_d023_s0_flat00
/-- Pinned raw matrix row 214, raw column 215, flat 1. -/
theorem p0_d023_s1_flat01 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 94 - 7^(1+1)*pw0 92) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0094, pw0_0092, pw0_0002, pw0_0000]
  decide
#print axioms p0_d023_s1_flat01
/-- Pinned raw matrix row 216, raw column 215, flat 1. -/
theorem p2_d023_s1_flat01 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 94 - 7^(1+1)*pw2 92) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0094, pw2_0092, pw2_0002, pw2_0000]
  decide
#print axioms p2_d023_s1_flat01
/-- Pinned raw matrix row 214, raw column 216, flat 2. -/
theorem p0_d023_s2_flat02 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 2 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 95 - 7^(2+1)*pw0 92) - (pw0 3 - 7^(2+1)*pw0 0) = 0
  rw [pw0_0095, pw0_0092, pw0_0003, pw0_0000]
  decide
#print axioms p0_d023_s2_flat02
/-- Pinned raw matrix row 216, raw column 216, flat 2. -/
theorem p2_d023_s2_flat02 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 2 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 95 - 7^(2+1)*pw2 92) - (pw2 3 - 7^(2+1)*pw2 0) = 0
  rw [pw2_0095, pw2_0092, pw2_0003, pw2_0000]
  decide
#print axioms p2_d023_s2_flat02
/-- Pinned raw matrix row 214, raw column 217, flat 3. -/
theorem p0_d024_s0_flat03 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 97 - 7^(0+1)*pw0 96) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0097, pw0_0096, pw0_0001, pw0_0000]
  decide
#print axioms p0_d024_s0_flat03
/-- Pinned raw matrix row 216, raw column 217, flat 3. -/
theorem p2_d024_s0_flat03 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 97 - 7^(0+1)*pw2 96) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0097, pw2_0096, pw2_0001, pw2_0000]
  decide
#print axioms p2_d024_s0_flat03
/-- Pinned raw matrix row 214, raw column 218, flat 4. -/
theorem p0_d024_s1_flat04 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 98 - 7^(1+1)*pw0 96) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0098, pw0_0096, pw0_0002, pw0_0000]
  decide
#print axioms p0_d024_s1_flat04
/-- Pinned raw matrix row 216, raw column 218, flat 4. -/
theorem p2_d024_s1_flat04 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 98 - 7^(1+1)*pw2 96) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0098, pw2_0096, pw2_0002, pw2_0000]
  decide
#print axioms p2_d024_s1_flat04
/-- Pinned raw matrix row 214, raw column 219, flat 5. -/
theorem p0_d024_s2_flat05 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 2 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 99 - 7^(2+1)*pw0 96) - (pw0 3 - 7^(2+1)*pw0 0) = 0
  rw [pw0_0099, pw0_0096, pw0_0003, pw0_0000]
  decide
#print axioms p0_d024_s2_flat05
/-- Pinned raw matrix row 216, raw column 219, flat 5. -/
theorem p2_d024_s2_flat05 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 24 2 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 99 - 7^(2+1)*pw2 96) - (pw2 3 - 7^(2+1)*pw2 0) = 0
  rw [pw2_0099, pw2_0096, pw2_0003, pw2_0000]
  decide
#print axioms p2_d024_s2_flat05
/-- Pinned raw matrix row 214, raw column 34, flat 6. -/
theorem p0_d046_s0_flat06 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 46 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 185 - 7^(0+1)*pw0 184) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0185, pw0_0184, pw0_0001, pw0_0000]
  decide
#print axioms p0_d046_s0_flat06
/-- Pinned raw matrix row 216, raw column 34, flat 6. -/
theorem p2_d046_s0_flat06 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 46 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 185 - 7^(0+1)*pw2 184) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0185, pw2_0184, pw2_0001, pw2_0000]
  decide
#print axioms p2_d046_s0_flat06
/-- Pinned raw matrix row 214, raw column 31, flat 7. -/
theorem p0_d044_s0_flat07 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 177 - 7^(0+1)*pw0 176) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0177, pw0_0176, pw0_0001, pw0_0000]
  decide
#print axioms p0_d044_s0_flat07
/-- Pinned raw matrix row 216, raw column 31, flat 7. -/
theorem p2_d044_s0_flat07 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 44 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 177 - 7^(0+1)*pw2 176) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0177, pw2_0176, pw2_0001, pw2_0000]
  decide
#print axioms p2_d044_s0_flat07
end AspisV8R19.R806Point02SelectedChunk00
