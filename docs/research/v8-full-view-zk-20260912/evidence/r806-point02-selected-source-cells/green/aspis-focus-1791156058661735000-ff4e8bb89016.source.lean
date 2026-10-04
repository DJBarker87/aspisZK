import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk05P0
import AspisV8R19.R780Point02WeightChunk05P2
import AspisV8R19.R780Point02WeightChunk06P0
import AspisV8R19.R780Point02WeightChunk06P2
import AspisV8R19.R780Point02WeightChunk17P0
import AspisV8R19.R780Point02WeightChunk17P2
import AspisV8R19.R780Point02WeightChunk18P0
import AspisV8R19.R780Point02WeightChunk18P2
import AspisV8R19.R780Point02WeightChunk19P0
import AspisV8R19.R780Point02WeightChunk19P2
import AspisV8R19.R780Point02WeightChunk20P0
import AspisV8R19.R780Point02WeightChunk20P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk05P0
open AspisV8R19.R780Point02WeightChunk05P2
open AspisV8R19.R780Point02WeightChunk06P0
open AspisV8R19.R780Point02WeightChunk06P2
open AspisV8R19.R780Point02WeightChunk17P0
open AspisV8R19.R780Point02WeightChunk17P2
open AspisV8R19.R780Point02WeightChunk18P0
open AspisV8R19.R780Point02WeightChunk18P2
open AspisV8R19.R780Point02WeightChunk19P0
open AspisV8R19.R780Point02WeightChunk19P2
open AspisV8R19.R780Point02WeightChunk20P0
open AspisV8R19.R780Point02WeightChunk20P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk05
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 5, flat 40. -/
theorem p0_d031_s0_flat40 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 0 (.inr (.inl 0)) = 4320 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 125 - 7^(0+1)*pw0 124) - (pw0 1 - 7^(0+1)*pw0 0) = 4320
  rw [pw0_0125, pw0_0124, pw0_0001, pw0_0000]
  decide
#print axioms p0_d031_s0_flat40
/-- Pinned raw matrix row 216, raw column 5, flat 40. -/
theorem p2_d031_s0_flat40 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 0 (.inr (.inl 2)) = 12960 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 125 - 7^(0+1)*pw2 124) - (pw2 1 - 7^(0+1)*pw2 0) = 12960
  rw [pw2_0125, pw2_0124, pw2_0001, pw2_0000]
  decide
#print axioms p2_d031_s0_flat40
/-- Pinned raw matrix row 214, raw column 6, flat 41. -/
theorem p0_d031_s1_flat41 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 1 (.inr (.inl 0)) = 21888 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 126 - 7^(1+1)*pw0 124) - (pw0 2 - 7^(1+1)*pw0 0) = 21888
  rw [pw0_0126, pw0_0124, pw0_0002, pw0_0000]
  decide
#print axioms p0_d031_s1_flat41
/-- Pinned raw matrix row 216, raw column 6, flat 41. -/
theorem p2_d031_s1_flat41 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 1 (.inr (.inl 2)) = 65664 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 126 - 7^(1+1)*pw2 124) - (pw2 2 - 7^(1+1)*pw2 0) = 65664
  rw [pw2_0126, pw2_0124, pw2_0002, pw2_0000]
  decide
#print axioms p2_d031_s1_flat41
/-- Pinned raw matrix row 214, raw column 36, flat 42. -/
theorem p0_d048_s1_flat42 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 48 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 194 - 7^(1+1)*pw0 192) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0194, pw0_0192, pw0_0002, pw0_0000]
  decide
#print axioms p0_d048_s1_flat42
/-- Pinned raw matrix row 216, raw column 36, flat 42. -/
theorem p2_d048_s1_flat42 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 48 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 194 - 7^(1+1)*pw2 192) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0194, pw2_0192, pw2_0002, pw2_0000]
  decide
#print axioms p2_d048_s1_flat42
/-- Pinned raw matrix row 214, raw column 37, flat 43. -/
theorem p0_d049_s0_flat43 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 197 - 7^(0+1)*pw0 196) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0197, pw0_0196, pw0_0001, pw0_0000]
  decide
#print axioms p0_d049_s0_flat43
/-- Pinned raw matrix row 216, raw column 37, flat 43. -/
theorem p2_d049_s0_flat43 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 197 - 7^(0+1)*pw2 196) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0197, pw2_0196, pw2_0001, pw2_0000]
  decide
#print axioms p2_d049_s0_flat43
/-- Pinned raw matrix row 214, raw column 38, flat 44. -/
theorem p0_d049_s1_flat44 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 198 - 7^(1+1)*pw0 196) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0198, pw0_0196, pw0_0002, pw0_0000]
  decide
#print axioms p0_d049_s1_flat44
/-- Pinned raw matrix row 216, raw column 38, flat 44. -/
theorem p2_d049_s1_flat44 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 198 - 7^(1+1)*pw2 196) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0198, pw2_0196, pw2_0002, pw2_0000]
  decide
#print axioms p2_d049_s1_flat44
/-- Pinned raw matrix row 214, raw column 39, flat 45. -/
theorem p0_d050_s0_flat45 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 201 - 7^(0+1)*pw0 200) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0201, pw0_0200, pw0_0001, pw0_0000]
  decide
#print axioms p0_d050_s0_flat45
/-- Pinned raw matrix row 216, raw column 39, flat 45. -/
theorem p2_d050_s0_flat45 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 201 - 7^(0+1)*pw2 200) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0201, pw2_0200, pw2_0001, pw2_0000]
  decide
#print axioms p2_d050_s0_flat45
/-- Pinned raw matrix row 214, raw column 40, flat 46. -/
theorem p0_d050_s1_flat46 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 202 - 7^(1+1)*pw0 200) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0202, pw0_0200, pw0_0002, pw0_0000]
  decide
#print axioms p0_d050_s1_flat46
/-- Pinned raw matrix row 216, raw column 40, flat 46. -/
theorem p2_d050_s1_flat46 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 202 - 7^(1+1)*pw2 200) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0202, pw2_0200, pw2_0002, pw2_0000]
  decide
#print axioms p2_d050_s1_flat46
/-- Pinned raw matrix row 214, raw column 41, flat 47. -/
theorem p0_d051_s0_flat47 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 205 - 7^(0+1)*pw0 204) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0205, pw0_0204, pw0_0001, pw0_0000]
  decide
#print axioms p0_d051_s0_flat47
/-- Pinned raw matrix row 216, raw column 41, flat 47. -/
theorem p2_d051_s0_flat47 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 205 - 7^(0+1)*pw2 204) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0205, pw2_0204, pw2_0001, pw2_0000]
  decide
#print axioms p2_d051_s0_flat47
end AspisV8R19.R806Point02SelectedChunk05
