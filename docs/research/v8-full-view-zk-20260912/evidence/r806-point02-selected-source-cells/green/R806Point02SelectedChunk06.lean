import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk19P0
import AspisV8R19.R780Point02WeightChunk19P2
import AspisV8R19.R780Point02WeightChunk20P0
import AspisV8R19.R780Point02WeightChunk20P2
import AspisV8R19.R780Point02WeightChunk21P0
import AspisV8R19.R780Point02WeightChunk21P2
import AspisV8R19.R780Point02WeightChunk22P0
import AspisV8R19.R780Point02WeightChunk22P2
import AspisV8R19.R780Point02WeightChunk23P0
import AspisV8R19.R780Point02WeightChunk23P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk19P0
open AspisV8R19.R780Point02WeightChunk19P2
open AspisV8R19.R780Point02WeightChunk20P0
open AspisV8R19.R780Point02WeightChunk20P2
open AspisV8R19.R780Point02WeightChunk21P0
open AspisV8R19.R780Point02WeightChunk21P2
open AspisV8R19.R780Point02WeightChunk22P0
open AspisV8R19.R780Point02WeightChunk22P2
open AspisV8R19.R780Point02WeightChunk23P0
open AspisV8R19.R780Point02WeightChunk23P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk06
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 42, flat 48. -/
theorem p0_d051_s1_flat48 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 206 - 7^(1+1)*pw0 204) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0206, pw0_0204, pw0_0002, pw0_0000]
  decide
#print axioms p0_d051_s1_flat48
/-- Pinned raw matrix row 216, raw column 42, flat 48. -/
theorem p2_d051_s1_flat48 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 206 - 7^(1+1)*pw2 204) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0206, pw2_0204, pw2_0002, pw2_0000]
  decide
#print axioms p2_d051_s1_flat48
/-- Pinned raw matrix row 214, raw column 43, flat 49. -/
theorem p0_d052_s0_flat49 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 209 - 7^(0+1)*pw0 208) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0209, pw0_0208, pw0_0001, pw0_0000]
  decide
#print axioms p0_d052_s0_flat49
/-- Pinned raw matrix row 216, raw column 43, flat 49. -/
theorem p2_d052_s0_flat49 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 209 - 7^(0+1)*pw2 208) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0209, pw2_0208, pw2_0001, pw2_0000]
  decide
#print axioms p2_d052_s0_flat49
/-- Pinned raw matrix row 214, raw column 44, flat 50. -/
theorem p0_d052_s1_flat50 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 210 - 7^(1+1)*pw0 208) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0210, pw0_0208, pw0_0002, pw0_0000]
  decide
#print axioms p0_d052_s1_flat50
/-- Pinned raw matrix row 216, raw column 44, flat 50. -/
theorem p2_d052_s1_flat50 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 210 - 7^(1+1)*pw2 208) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0210, pw2_0208, pw2_0002, pw2_0000]
  decide
#print axioms p2_d052_s1_flat50
/-- Pinned raw matrix row 214, raw column 45, flat 51. -/
theorem p0_d053_s0_flat51 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 213 - 7^(0+1)*pw0 212) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0213, pw0_0212, pw0_0001, pw0_0000]
  decide
#print axioms p0_d053_s0_flat51
/-- Pinned raw matrix row 216, raw column 45, flat 51. -/
theorem p2_d053_s0_flat51 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 213 - 7^(0+1)*pw2 212) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0213, pw2_0212, pw2_0001, pw2_0000]
  decide
#print axioms p2_d053_s0_flat51
/-- Pinned raw matrix row 214, raw column 46, flat 52. -/
theorem p0_d053_s1_flat52 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 214 - 7^(1+1)*pw0 212) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0214, pw0_0212, pw0_0002, pw0_0000]
  decide
#print axioms p0_d053_s1_flat52
/-- Pinned raw matrix row 216, raw column 46, flat 52. -/
theorem p2_d053_s1_flat52 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 214 - 7^(1+1)*pw2 212) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0214, pw2_0212, pw2_0002, pw2_0000]
  decide
#print axioms p2_d053_s1_flat52
/-- Pinned raw matrix row 214, raw column 47, flat 53. -/
theorem p0_d054_s0_flat53 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 217 - 7^(0+1)*pw0 216) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0217, pw0_0216, pw0_0001, pw0_0000]
  decide
#print axioms p0_d054_s0_flat53
/-- Pinned raw matrix row 216, raw column 47, flat 53. -/
theorem p2_d054_s0_flat53 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 217 - 7^(0+1)*pw2 216) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0217, pw2_0216, pw2_0001, pw2_0000]
  decide
#print axioms p2_d054_s0_flat53
/-- Pinned raw matrix row 214, raw column 48, flat 54. -/
theorem p0_d054_s1_flat54 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 218 - 7^(1+1)*pw0 216) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0218, pw0_0216, pw0_0002, pw0_0000]
  decide
#print axioms p0_d054_s1_flat54
/-- Pinned raw matrix row 216, raw column 48, flat 54. -/
theorem p2_d054_s1_flat54 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 218 - 7^(1+1)*pw2 216) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0218, pw2_0216, pw2_0002, pw2_0000]
  decide
#print axioms p2_d054_s1_flat54
/-- Pinned raw matrix row 214, raw column 49, flat 55. -/
theorem p0_d055_s0_flat55 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 0 (.inr (.inl 0)) = 1610612724 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 221 - 7^(0+1)*pw0 220) - (pw0 1 - 7^(0+1)*pw0 0) = 1610612724
  rw [pw0_0221, pw0_0220, pw0_0001, pw0_0000]
  decide
#print axioms p0_d055_s0_flat55
/-- Pinned raw matrix row 216, raw column 49, flat 55. -/
theorem p2_d055_s0_flat55 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 0 (.inr (.inl 2)) = 536870908 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 221 - 7^(0+1)*pw2 220) - (pw2 1 - 7^(0+1)*pw2 0) = 536870908
  rw [pw2_0221, pw2_0220, pw2_0001, pw2_0000]
  decide
#print axioms p2_d055_s0_flat55
end AspisV8R19.R806Point02SelectedChunk06
