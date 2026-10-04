import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk25P0
import AspisV8R19.R780Point02WeightChunk25P2
import AspisV8R19.R780Point02WeightChunk26P0
import AspisV8R19.R780Point02WeightChunk26P2
import AspisV8R19.R780Point02WeightChunk27P0
import AspisV8R19.R780Point02WeightChunk27P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk25P0
open AspisV8R19.R780Point02WeightChunk25P2
open AspisV8R19.R780Point02WeightChunk26P0
open AspisV8R19.R780Point02WeightChunk26P2
open AspisV8R19.R780Point02WeightChunk27P0
open AspisV8R19.R780Point02WeightChunk27P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk08
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 58, flat 64. -/
theorem p0_d059_s1_flat64 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 1 (.inr (.inl 0)) = 27054 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 238 - 7^(1+1)*pw0 236) - (pw0 2 - 7^(1+1)*pw0 0) = 27054
  rw [pw0_0238, pw0_0236, pw0_0002, pw0_0000]
  decide
#print axioms p0_d059_s1_flat64
/-- Pinned raw matrix row 216, raw column 58, flat 64. -/
theorem p2_d059_s1_flat64 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 1 (.inr (.inl 2)) = 9018 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 238 - 7^(1+1)*pw2 236) - (pw2 2 - 7^(1+1)*pw2 0) = 9018
  rw [pw2_0238, pw2_0236, pw2_0002, pw2_0000]
  decide
#print axioms p2_d059_s1_flat64
/-- Pinned raw matrix row 214, raw column 59, flat 65. -/
theorem p0_d060_s0_flat65 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 0 (.inr (.inl 0)) = 2147480131 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 241 - 7^(0+1)*pw0 240) - (pw0 1 - 7^(0+1)*pw0 0) = 2147480131
  rw [pw0_0241, pw0_0240, pw0_0001, pw0_0000]
  decide
#print axioms p0_d060_s0_flat65
/-- Pinned raw matrix row 216, raw column 59, flat 65. -/
theorem p2_d060_s0_flat65 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 0 (.inr (.inl 2)) = 2147482475 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 241 - 7^(0+1)*pw2 240) - (pw2 1 - 7^(0+1)*pw2 0) = 2147482475
  rw [pw2_0241, pw2_0240, pw2_0001, pw2_0000]
  decide
#print axioms p2_d060_s0_flat65
/-- Pinned raw matrix row 214, raw column 60, flat 66. -/
theorem p0_d060_s2_flat66 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 2 (.inr (.inl 0)) = 2147313751 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 243 - 7^(2+1)*pw0 240) - (pw0 3 - 7^(2+1)*pw0 0) = 2147313751
  rw [pw0_0243, pw0_0240, pw0_0003, pw0_0000]
  decide
#print axioms p0_d060_s2_flat66
/-- Pinned raw matrix row 216, raw column 60, flat 66. -/
theorem p2_d060_s2_flat66 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 2 (.inr (.inl 2)) = 2147427015 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 243 - 7^(2+1)*pw2 240) - (pw2 3 - 7^(2+1)*pw2 0) = 2147427015
  rw [pw2_0243, pw2_0240, pw2_0003, pw2_0000]
  decide
#print axioms p2_d060_s2_flat66
/-- Pinned raw matrix row 214, raw column 61, flat 67. -/
theorem p0_d061_s0_flat67 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 0 (.inr (.inl 0)) = 4323 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 245 - 7^(0+1)*pw0 244) - (pw0 1 - 7^(0+1)*pw0 0) = 4323
  rw [pw0_0245, pw0_0244, pw0_0001, pw0_0000]
  decide
#print axioms p0_d061_s0_flat67
/-- Pinned raw matrix row 216, raw column 61, flat 67. -/
theorem p2_d061_s0_flat67 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 0 (.inr (.inl 2)) = 1441 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 245 - 7^(0+1)*pw2 244) - (pw2 1 - 7^(0+1)*pw2 0) = 1441
  rw [pw2_0245, pw2_0244, pw2_0001, pw2_0000]
  decide
#print axioms p2_d061_s0_flat67
/-- Pinned raw matrix row 214, raw column 62, flat 68. -/
theorem p0_d061_s2_flat68 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 2 (.inr (.inl 0)) = 227988 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 247 - 7^(2+1)*pw0 244) - (pw0 3 - 7^(2+1)*pw0 0) = 227988
  rw [pw0_0247, pw0_0244, pw0_0003, pw0_0000]
  decide
#print axioms p0_d061_s2_flat68
/-- Pinned raw matrix row 216, raw column 62, flat 68. -/
theorem p2_d061_s2_flat68 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 2 (.inr (.inl 2)) = 75996 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 247 - 7^(2+1)*pw2 244) - (pw2 3 - 7^(2+1)*pw2 0) = 75996
  rw [pw2_0247, pw2_0244, pw2_0003, pw2_0000]
  decide
#print axioms p2_d061_s2_flat68
/-- Pinned raw matrix row 214, raw column 63, flat 69. -/
theorem p0_d062_s0_flat69 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 0 (.inr (.inl 0)) = 5274 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 249 - 7^(0+1)*pw0 248) - (pw0 1 - 7^(0+1)*pw0 0) = 5274
  rw [pw0_0249, pw0_0248, pw0_0001, pw0_0000]
  decide
#print axioms p0_d062_s0_flat69
/-- Pinned raw matrix row 216, raw column 63, flat 69. -/
theorem p2_d062_s0_flat69 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 0 (.inr (.inl 2)) = 1758 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 249 - 7^(0+1)*pw2 248) - (pw2 1 - 7^(0+1)*pw2 0) = 1758
  rw [pw2_0249, pw2_0248, pw2_0001, pw2_0000]
  decide
#print axioms p2_d062_s0_flat69
/-- Pinned raw matrix row 214, raw column 64, flat 70. -/
theorem p0_d062_s2_flat70 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 2 (.inr (.inl 0)) = 254844 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 251 - 7^(2+1)*pw0 248) - (pw0 3 - 7^(2+1)*pw0 0) = 254844
  rw [pw0_0251, pw0_0248, pw0_0003, pw0_0000]
  decide
#print axioms p0_d062_s2_flat70
/-- Pinned raw matrix row 216, raw column 64, flat 70. -/
theorem p2_d062_s2_flat70 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 2 (.inr (.inl 2)) = 84948 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 251 - 7^(2+1)*pw2 248) - (pw2 3 - 7^(2+1)*pw2 0) = 84948
  rw [pw2_0251, pw2_0248, pw2_0003, pw2_0000]
  decide
#print axioms p2_d062_s2_flat70
/-- Pinned raw matrix row 214, raw column 65, flat 71. -/
theorem p0_d063_s0_flat71 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 63 0 (.inr (.inl 0)) = 1610606082 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 253 - 7^(0+1)*pw0 252) - (pw0 1 - 7^(0+1)*pw0 0) = 1610606082
  rw [pw0_0253, pw0_0252, pw0_0001, pw0_0000]
  decide
#print axioms p0_d063_s0_flat71
/-- Pinned raw matrix row 216, raw column 65, flat 71. -/
theorem p2_d063_s0_flat71 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 63 0 (.inr (.inl 2)) = 536868694 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 253 - 7^(0+1)*pw2 252) - (pw2 1 - 7^(0+1)*pw2 0) = 536868694
  rw [pw2_0253, pw2_0252, pw2_0001, pw2_0000]
  decide
#print axioms p2_d063_s0_flat71
end AspisV8R19.R806Point02SelectedChunk08
