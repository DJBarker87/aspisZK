import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk22P0
import AspisV8R19.R780Point02WeightChunk22P2
import AspisV8R19.R780Point02WeightChunk23P0
import AspisV8R19.R780Point02WeightChunk23P2
import AspisV8R19.R780Point02WeightChunk24P0
import AspisV8R19.R780Point02WeightChunk24P2
import AspisV8R19.R780Point02WeightChunk25P0
import AspisV8R19.R780Point02WeightChunk25P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk22P0
open AspisV8R19.R780Point02WeightChunk22P2
open AspisV8R19.R780Point02WeightChunk23P0
open AspisV8R19.R780Point02WeightChunk23P2
open AspisV8R19.R780Point02WeightChunk24P0
open AspisV8R19.R780Point02WeightChunk24P2
open AspisV8R19.R780Point02WeightChunk25P0
open AspisV8R19.R780Point02WeightChunk25P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk07
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 50, flat 56. -/
theorem p0_d055_s1_flat56 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 1 (.inr (.inl 0)) = 1610612724 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 222 - 7^(1+1)*pw0 220) - (pw0 2 - 7^(1+1)*pw0 0) = 1610612724
  rw [pw0_0222, pw0_0220, pw0_0002, pw0_0000]
  decide
#print axioms p0_d055_s1_flat56
/-- Pinned raw matrix row 216, raw column 50, flat 56. -/
theorem p2_d055_s1_flat56 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 1 (.inr (.inl 2)) = 536870908 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 222 - 7^(1+1)*pw2 220) - (pw2 2 - 7^(1+1)*pw2 0) = 536870908
  rw [pw2_0222, pw2_0220, pw2_0002, pw2_0000]
  decide
#print axioms p2_d055_s1_flat56
/-- Pinned raw matrix row 214, raw column 51, flat 57. -/
theorem p0_d056_s0_flat57 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 0 (.inr (.inl 0)) = 1758 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 225 - 7^(0+1)*pw0 224) - (pw0 1 - 7^(0+1)*pw0 0) = 1758
  rw [pw0_0225, pw0_0224, pw0_0001, pw0_0000]
  decide
#print axioms p0_d056_s0_flat57
/-- Pinned raw matrix row 216, raw column 51, flat 57. -/
theorem p2_d056_s0_flat57 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 0 (.inr (.inl 2)) = 586 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 225 - 7^(0+1)*pw2 224) - (pw2 1 - 7^(0+1)*pw2 0) = 586
  rw [pw2_0225, pw2_0224, pw2_0001, pw2_0000]
  decide
#print axioms p2_d056_s0_flat57
/-- Pinned raw matrix row 214, raw column 52, flat 58. -/
theorem p0_d056_s1_flat58 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 1 (.inr (.inl 0)) = 13602 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 226 - 7^(1+1)*pw0 224) - (pw0 2 - 7^(1+1)*pw0 0) = 13602
  rw [pw0_0226, pw0_0224, pw0_0002, pw0_0000]
  decide
#print axioms p0_d056_s1_flat58
/-- Pinned raw matrix row 216, raw column 52, flat 58. -/
theorem p2_d056_s1_flat58 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 1 (.inr (.inl 2)) = 4534 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 226 - 7^(1+1)*pw2 224) - (pw2 2 - 7^(1+1)*pw2 0) = 4534
  rw [pw2_0226, pw2_0224, pw2_0002, pw2_0000]
  decide
#print axioms p2_d056_s1_flat58
/-- Pinned raw matrix row 214, raw column 53, flat 59. -/
theorem p0_d057_s0_flat59 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 0 (.inr (.inl 0)) = 1073739662 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 229 - 7^(0+1)*pw0 228) - (pw0 1 - 7^(0+1)*pw0 0) = 1073739662
  rw [pw0_0229, pw0_0228, pw0_0001, pw0_0000]
  decide
#print axioms p0_d057_s0_flat59
/-- Pinned raw matrix row 216, raw column 53, flat 59. -/
theorem p2_d057_s0_flat59 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 0 (.inr (.inl 2)) = 1073741103 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 229 - 7^(0+1)*pw2 228) - (pw2 1 - 7^(0+1)*pw2 0) = 1073741103
  rw [pw2_0229, pw2_0228, pw2_0001, pw2_0000]
  decide
#print axioms p2_d057_s0_flat59
/-- Pinned raw matrix row 214, raw column 54, flat 60. -/
theorem p0_d057_s1_flat60 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 1 (.inr (.inl 0)) = 1073723870 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 230 - 7^(1+1)*pw0 228) - (pw0 2 - 7^(1+1)*pw0 0) = 1073723870
  rw [pw0_0230, pw0_0228, pw0_0002, pw0_0000]
  decide
#print axioms p0_d057_s1_flat60
/-- Pinned raw matrix row 216, raw column 54, flat 60. -/
theorem p2_d057_s1_flat60 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 1 (.inr (.inl 2)) = 1073735839 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 230 - 7^(1+1)*pw2 228) - (pw2 2 - 7^(1+1)*pw2 0) = 1073735839
  rw [pw2_0230, pw2_0228, pw2_0002, pw2_0000]
  decide
#print axioms p2_d057_s1_flat60
/-- Pinned raw matrix row 214, raw column 55, flat 61. -/
theorem p0_d058_s0_flat61 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 0 (.inr (.inl 0)) = 2147481010 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 233 - 7^(0+1)*pw0 232) - (pw0 1 - 7^(0+1)*pw0 0) = 2147481010
  rw [pw0_0233, pw0_0232, pw0_0001, pw0_0000]
  decide
#print axioms p0_d058_s0_flat61
/-- Pinned raw matrix row 216, raw column 55, flat 61. -/
theorem p2_d058_s0_flat61 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 0 (.inr (.inl 2)) = 2147482768 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 233 - 7^(0+1)*pw2 232) - (pw2 1 - 7^(0+1)*pw2 0) = 2147482768
  rw [pw2_0233, pw2_0232, pw2_0001, pw2_0000]
  decide
#print axioms p2_d058_s0_flat61
/-- Pinned raw matrix row 214, raw column 56, flat 62. -/
theorem p0_d058_s1_flat62 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 1 (.inr (.inl 0)) = 2147463244 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 234 - 7^(1+1)*pw0 232) - (pw0 2 - 7^(1+1)*pw0 0) = 2147463244
  rw [pw0_0234, pw0_0232, pw0_0002, pw0_0000]
  decide
#print axioms p0_d058_s1_flat62
/-- Pinned raw matrix row 216, raw column 56, flat 62. -/
theorem p2_d058_s1_flat62 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 1 (.inr (.inl 2)) = 2147476846 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 234 - 7^(1+1)*pw2 232) - (pw2 2 - 7^(1+1)*pw2 0) = 2147476846
  rw [pw2_0234, pw2_0232, pw2_0002, pw2_0000]
  decide
#print axioms p2_d058_s1_flat62
/-- Pinned raw matrix row 214, raw column 57, flat 63. -/
theorem p0_d059_s0_flat63 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 0 (.inr (.inl 0)) = 3366 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 237 - 7^(0+1)*pw0 236) - (pw0 1 - 7^(0+1)*pw0 0) = 3366
  rw [pw0_0237, pw0_0236, pw0_0001, pw0_0000]
  decide
#print axioms p0_d059_s0_flat63
/-- Pinned raw matrix row 216, raw column 57, flat 63. -/
theorem p2_d059_s0_flat63 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 0 (.inr (.inl 2)) = 1122 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 237 - 7^(0+1)*pw2 236) - (pw2 1 - 7^(0+1)*pw2 0) = 1122
  rw [pw2_0237, pw2_0236, pw2_0001, pw2_0000]
  decide
#print axioms p2_d059_s0_flat63
end AspisV8R19.R806Point02SelectedChunk07
