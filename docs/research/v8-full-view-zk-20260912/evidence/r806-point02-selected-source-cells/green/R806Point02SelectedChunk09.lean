import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk03P0
import AspisV8R19.R780Point02WeightChunk03P2
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
open AspisV8R19.R780Point02WeightChunk17P0
open AspisV8R19.R780Point02WeightChunk17P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk09
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 228, flat 72. -/
theorem p0_d027_s2_flat72 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 27 2 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 111 - 7^(2+1)*pw0 108) - (pw0 3 - 7^(2+1)*pw0 0) = 0
  rw [pw0_0111, pw0_0108, pw0_0003, pw0_0000]
  decide
#print axioms p0_d027_s2_flat72
/-- Pinned raw matrix row 216, raw column 228, flat 72. -/
theorem p2_d027_s2_flat72 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 27 2 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 111 - 7^(2+1)*pw2 108) - (pw2 3 - 7^(2+1)*pw2 0) = 0
  rw [pw2_0111, pw2_0108, pw2_0003, pw2_0000]
  decide
#print axioms p2_d027_s2_flat72
/-- Pinned raw matrix row 214, raw column 241, flat 73. -/
theorem p0_d047_s2_flat73 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 191 - 7^(2+1)*pw0 188) - (pw0 3 - 7^(2+1)*pw0 0) = 0
  rw [pw0_0191, pw0_0188, pw0_0003, pw0_0000]
  decide
#print axioms p0_d047_s2_flat73
/-- Pinned raw matrix row 216, raw column 241, flat 73. -/
theorem p2_d047_s2_flat73 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 191 - 7^(2+1)*pw2 188) - (pw2 3 - 7^(2+1)*pw2 0) = 0
  rw [pw2_0191, pw2_0188, pw2_0003, pw2_0000]
  decide
#print axioms p2_d047_s2_flat73
end AspisV8R19.R806Point02SelectedChunk09
