import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk06P0
import AspisV8R19.R780Point02WeightChunk06P2
import AspisV8R19.R780Point02WeightChunk07P0
import AspisV8R19.R780Point02WeightChunk07P2
import AspisV8R19.R780Point02WeightChunk08P0
import AspisV8R19.R780Point02WeightChunk08P2
import AspisV8R19.R780Point02WeightChunk14P0
import AspisV8R19.R780Point02WeightChunk14P2
import AspisV8R19.R780Point02WeightChunk15P0
import AspisV8R19.R780Point02WeightChunk15P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk06P0
open AspisV8R19.R780Point02WeightChunk06P2
open AspisV8R19.R780Point02WeightChunk07P0
open AspisV8R19.R780Point02WeightChunk07P2
open AspisV8R19.R780Point02WeightChunk08P0
open AspisV8R19.R780Point02WeightChunk08P2
open AspisV8R19.R780Point02WeightChunk14P0
open AspisV8R19.R780Point02WeightChunk14P2
open AspisV8R19.R780Point02WeightChunk15P0
open AspisV8R19.R780Point02WeightChunk15P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk02
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 29, flat 16. -/
theorem p0_d043_s0_flat16 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 173 - 7^(0+1)*pw0 172) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0173, pw0_0172, pw0_0001, pw0_0000]
  decide
#print axioms p0_d043_s0_flat16
/-- Pinned raw matrix row 216, raw column 29, flat 16. -/
theorem p2_d043_s0_flat16 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 173 - 7^(0+1)*pw2 172) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0173, pw2_0172, pw2_0001, pw2_0000]
  decide
#print axioms p2_d043_s0_flat16
/-- Pinned raw matrix row 214, raw column 30, flat 17. -/
theorem p0_d043_s1_flat17 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 174 - 7^(1+1)*pw0 172) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0174, pw0_0172, pw0_0002, pw0_0000]
  decide
#print axioms p0_d043_s1_flat17
/-- Pinned raw matrix row 216, raw column 30, flat 17. -/
theorem p2_d043_s1_flat17 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 43 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 174 - 7^(1+1)*pw2 172) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0174, pw2_0172, pw2_0002, pw2_0000]
  decide
#print axioms p2_d043_s1_flat17
/-- Pinned raw matrix row 214, raw column 7, flat 18. -/
theorem p0_d032_s0_flat18 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 129 - 7^(0+1)*pw0 128) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0129, pw0_0128, pw0_0001, pw0_0000]
  decide
#print axioms p0_d032_s0_flat18
/-- Pinned raw matrix row 216, raw column 7, flat 18. -/
theorem p2_d032_s0_flat18 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 129 - 7^(0+1)*pw2 128) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0129, pw2_0128, pw2_0001, pw2_0000]
  decide
#print axioms p2_d032_s0_flat18
/-- Pinned raw matrix row 214, raw column 8, flat 19. -/
theorem p0_d032_s1_flat19 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 130 - 7^(1+1)*pw0 128) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0130, pw0_0128, pw0_0002, pw0_0000]
  decide
#print axioms p0_d032_s1_flat19
/-- Pinned raw matrix row 216, raw column 8, flat 19. -/
theorem p2_d032_s1_flat19 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 32 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 130 - 7^(1+1)*pw2 128) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0130, pw2_0128, pw2_0002, pw2_0000]
  decide
#print axioms p2_d032_s1_flat19
/-- Pinned raw matrix row 214, raw column 9, flat 20. -/
theorem p0_d033_s0_flat20 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 133 - 7^(0+1)*pw0 132) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0133, pw0_0132, pw0_0001, pw0_0000]
  decide
#print axioms p0_d033_s0_flat20
/-- Pinned raw matrix row 216, raw column 9, flat 20. -/
theorem p2_d033_s0_flat20 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 133 - 7^(0+1)*pw2 132) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0133, pw2_0132, pw2_0001, pw2_0000]
  decide
#print axioms p2_d033_s0_flat20
/-- Pinned raw matrix row 214, raw column 10, flat 21. -/
theorem p0_d033_s1_flat21 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 134 - 7^(1+1)*pw0 132) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0134, pw0_0132, pw0_0002, pw0_0000]
  decide
#print axioms p0_d033_s1_flat21
/-- Pinned raw matrix row 216, raw column 10, flat 21. -/
theorem p2_d033_s1_flat21 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 33 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 134 - 7^(1+1)*pw2 132) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0134, pw2_0132, pw2_0002, pw2_0000]
  decide
#print axioms p2_d033_s1_flat21
/-- Pinned raw matrix row 214, raw column 11, flat 22. -/
theorem p0_d034_s0_flat22 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 137 - 7^(0+1)*pw0 136) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0137, pw0_0136, pw0_0001, pw0_0000]
  decide
#print axioms p0_d034_s0_flat22
/-- Pinned raw matrix row 216, raw column 11, flat 22. -/
theorem p2_d034_s0_flat22 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 137 - 7^(0+1)*pw2 136) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0137, pw2_0136, pw2_0001, pw2_0000]
  decide
#print axioms p2_d034_s0_flat22
/-- Pinned raw matrix row 214, raw column 12, flat 23. -/
theorem p0_d034_s1_flat23 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 138 - 7^(1+1)*pw0 136) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0138, pw0_0136, pw0_0002, pw0_0000]
  decide
#print axioms p0_d034_s1_flat23
/-- Pinned raw matrix row 216, raw column 12, flat 23. -/
theorem p2_d034_s1_flat23 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 34 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 138 - 7^(1+1)*pw2 136) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0138, pw2_0136, pw2_0002, pw2_0000]
  decide
#print axioms p2_d034_s1_flat23
end AspisV8R19.R806Point02SelectedChunk02
