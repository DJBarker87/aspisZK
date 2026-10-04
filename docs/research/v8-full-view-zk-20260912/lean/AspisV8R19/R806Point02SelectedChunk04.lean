import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk03P0
import AspisV8R19.R780Point02WeightChunk03P2
import AspisV8R19.R780Point02WeightChunk04P0
import AspisV8R19.R780Point02WeightChunk04P2
import AspisV8R19.R780Point02WeightChunk05P0
import AspisV8R19.R780Point02WeightChunk05P2
import AspisV8R19.R780Point02WeightChunk11P0
import AspisV8R19.R780Point02WeightChunk11P2
import AspisV8R19.R780Point02WeightChunk12P0
import AspisV8R19.R780Point02WeightChunk12P2
import AspisV8R19.R780Point02WeightChunk17P0
import AspisV8R19.R780Point02WeightChunk17P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk03P0
open AspisV8R19.R780Point02WeightChunk03P2
open AspisV8R19.R780Point02WeightChunk04P0
open AspisV8R19.R780Point02WeightChunk04P2
open AspisV8R19.R780Point02WeightChunk05P0
open AspisV8R19.R780Point02WeightChunk05P2
open AspisV8R19.R780Point02WeightChunk11P0
open AspisV8R19.R780Point02WeightChunk11P2
open AspisV8R19.R780Point02WeightChunk12P0
open AspisV8R19.R780Point02WeightChunk12P2
open AspisV8R19.R780Point02WeightChunk17P0
open AspisV8R19.R780Point02WeightChunk17P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk04
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 21, flat 32. -/
theorem p0_d039_s0_flat32 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 157 - 7^(0+1)*pw0 156) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0157, pw0_0156, pw0_0001, pw0_0000]
  decide
#print axioms p0_d039_s0_flat32
/-- Pinned raw matrix row 216, raw column 21, flat 32. -/
theorem p2_d039_s0_flat32 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 157 - 7^(0+1)*pw2 156) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0157, pw2_0156, pw2_0001, pw2_0000]
  decide
#print axioms p2_d039_s0_flat32
/-- Pinned raw matrix row 214, raw column 22, flat 33. -/
theorem p0_d039_s1_flat33 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 158 - 7^(1+1)*pw0 156) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0158, pw0_0156, pw0_0002, pw0_0000]
  decide
#print axioms p0_d039_s1_flat33
/-- Pinned raw matrix row 216, raw column 22, flat 33. -/
theorem p2_d039_s1_flat33 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 39 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 158 - 7^(1+1)*pw2 156) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0158, pw2_0156, pw2_0002, pw2_0000]
  decide
#print axioms p2_d039_s1_flat33
/-- Pinned raw matrix row 214, raw column 35, flat 34. -/
theorem p0_d047_s1_flat34 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 190 - 7^(1+1)*pw0 188) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0190, pw0_0188, pw0_0002, pw0_0000]
  decide
#print axioms p0_d047_s1_flat34
/-- Pinned raw matrix row 216, raw column 35, flat 34. -/
theorem p2_d047_s1_flat34 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 190 - 7^(1+1)*pw2 188) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0190, pw2_0188, pw2_0002, pw2_0000]
  decide
#print axioms p2_d047_s1_flat34
/-- Pinned raw matrix row 214, raw column 0, flat 35. -/
theorem p0_d028_s1_flat35 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 114 - 7^(1+1)*pw0 112) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0114, pw0_0112, pw0_0002, pw0_0000]
  decide
#print axioms p0_d028_s1_flat35
/-- Pinned raw matrix row 216, raw column 0, flat 35. -/
theorem p2_d028_s1_flat35 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 114 - 7^(1+1)*pw2 112) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0114, pw2_0112, pw2_0002, pw2_0000]
  decide
#print axioms p2_d028_s1_flat35
/-- Pinned raw matrix row 214, raw column 1, flat 36. -/
theorem p0_d029_s0_flat36 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 117 - 7^(0+1)*pw0 116) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0117, pw0_0116, pw0_0001, pw0_0000]
  decide
#print axioms p0_d029_s0_flat36
/-- Pinned raw matrix row 216, raw column 1, flat 36. -/
theorem p2_d029_s0_flat36 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 117 - 7^(0+1)*pw2 116) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0117, pw2_0116, pw2_0001, pw2_0000]
  decide
#print axioms p2_d029_s0_flat36
/-- Pinned raw matrix row 214, raw column 2, flat 37. -/
theorem p0_d029_s1_flat37 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 118 - 7^(1+1)*pw0 116) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0118, pw0_0116, pw0_0002, pw0_0000]
  decide
#print axioms p0_d029_s1_flat37
/-- Pinned raw matrix row 216, raw column 2, flat 37. -/
theorem p2_d029_s1_flat37 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 118 - 7^(1+1)*pw2 116) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0118, pw2_0116, pw2_0002, pw2_0000]
  decide
#print axioms p2_d029_s1_flat37
/-- Pinned raw matrix row 214, raw column 3, flat 38. -/
theorem p0_d030_s0_flat38 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 121 - 7^(0+1)*pw0 120) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0121, pw0_0120, pw0_0001, pw0_0000]
  decide
#print axioms p0_d030_s0_flat38
/-- Pinned raw matrix row 216, raw column 3, flat 38. -/
theorem p2_d030_s0_flat38 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 121 - 7^(0+1)*pw2 120) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0121, pw2_0120, pw2_0001, pw2_0000]
  decide
#print axioms p2_d030_s0_flat38
/-- Pinned raw matrix row 214, raw column 4, flat 39. -/
theorem p0_d030_s1_flat39 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 122 - 7^(1+1)*pw0 120) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0122, pw0_0120, pw0_0002, pw0_0000]
  decide
#print axioms p0_d030_s1_flat39
/-- Pinned raw matrix row 216, raw column 4, flat 39. -/
theorem p2_d030_s1_flat39 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 122 - 7^(1+1)*pw2 120) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0122, pw2_0120, pw2_0002, pw2_0000]
  decide
#print axioms p2_d030_s1_flat39
end AspisV8R19.R806Point02SelectedChunk04
