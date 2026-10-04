import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P0
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk08P0
import AspisV8R19.R780Point02WeightChunk08P2
import AspisV8R19.R780Point02WeightChunk09P0
import AspisV8R19.R780Point02WeightChunk09P2
import AspisV8R19.R780Point02WeightChunk10P0
import AspisV8R19.R780Point02WeightChunk10P2
import AspisV8R19.R780Point02WeightChunk11P0
import AspisV8R19.R780Point02WeightChunk11P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P0
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk08P0
open AspisV8R19.R780Point02WeightChunk08P2
open AspisV8R19.R780Point02WeightChunk09P0
open AspisV8R19.R780Point02WeightChunk09P2
open AspisV8R19.R780Point02WeightChunk10P0
open AspisV8R19.R780Point02WeightChunk10P2
open AspisV8R19.R780Point02WeightChunk11P0
open AspisV8R19.R780Point02WeightChunk11P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806Point02SelectedChunk03
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
/-- Pinned raw matrix row 214, raw column 13, flat 24. -/
theorem p0_d035_s0_flat24 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 141 - 7^(0+1)*pw0 140) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0141, pw0_0140, pw0_0001, pw0_0000]
  decide
#print axioms p0_d035_s0_flat24
/-- Pinned raw matrix row 216, raw column 13, flat 24. -/
theorem p2_d035_s0_flat24 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 141 - 7^(0+1)*pw2 140) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0141, pw2_0140, pw2_0001, pw2_0000]
  decide
#print axioms p2_d035_s0_flat24
/-- Pinned raw matrix row 214, raw column 14, flat 25. -/
theorem p0_d035_s1_flat25 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 142 - 7^(1+1)*pw0 140) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0142, pw0_0140, pw0_0002, pw0_0000]
  decide
#print axioms p0_d035_s1_flat25
/-- Pinned raw matrix row 216, raw column 14, flat 25. -/
theorem p2_d035_s1_flat25 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 35 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 142 - 7^(1+1)*pw2 140) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0142, pw2_0140, pw2_0002, pw2_0000]
  decide
#print axioms p2_d035_s1_flat25
/-- Pinned raw matrix row 214, raw column 15, flat 26. -/
theorem p0_d036_s0_flat26 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 145 - 7^(0+1)*pw0 144) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0145, pw0_0144, pw0_0001, pw0_0000]
  decide
#print axioms p0_d036_s0_flat26
/-- Pinned raw matrix row 216, raw column 15, flat 26. -/
theorem p2_d036_s0_flat26 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 145 - 7^(0+1)*pw2 144) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0145, pw2_0144, pw2_0001, pw2_0000]
  decide
#print axioms p2_d036_s0_flat26
/-- Pinned raw matrix row 214, raw column 16, flat 27. -/
theorem p0_d036_s1_flat27 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 146 - 7^(1+1)*pw0 144) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0146, pw0_0144, pw0_0002, pw0_0000]
  decide
#print axioms p0_d036_s1_flat27
/-- Pinned raw matrix row 216, raw column 16, flat 27. -/
theorem p2_d036_s1_flat27 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 36 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 146 - 7^(1+1)*pw2 144) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0146, pw2_0144, pw2_0002, pw2_0000]
  decide
#print axioms p2_d036_s1_flat27
/-- Pinned raw matrix row 214, raw column 17, flat 28. -/
theorem p0_d037_s0_flat28 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 149 - 7^(0+1)*pw0 148) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0149, pw0_0148, pw0_0001, pw0_0000]
  decide
#print axioms p0_d037_s0_flat28
/-- Pinned raw matrix row 216, raw column 17, flat 28. -/
theorem p2_d037_s0_flat28 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 149 - 7^(0+1)*pw2 148) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0149, pw2_0148, pw2_0001, pw2_0000]
  decide
#print axioms p2_d037_s0_flat28
/-- Pinned raw matrix row 214, raw column 18, flat 29. -/
theorem p0_d037_s1_flat29 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 150 - 7^(1+1)*pw0 148) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0150, pw0_0148, pw0_0002, pw0_0000]
  decide
#print axioms p0_d037_s1_flat29
/-- Pinned raw matrix row 216, raw column 18, flat 29. -/
theorem p2_d037_s1_flat29 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 37 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 150 - 7^(1+1)*pw2 148) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0150, pw2_0148, pw2_0002, pw2_0000]
  decide
#print axioms p2_d037_s1_flat29
/-- Pinned raw matrix row 214, raw column 19, flat 30. -/
theorem p0_d038_s0_flat30 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 0 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 153 - 7^(0+1)*pw0 152) - (pw0 1 - 7^(0+1)*pw0 0) = 0
  rw [pw0_0153, pw0_0152, pw0_0001, pw0_0000]
  decide
#print axioms p0_d038_s0_flat30
/-- Pinned raw matrix row 216, raw column 19, flat 30. -/
theorem p2_d038_s0_flat30 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 0 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 153 - 7^(0+1)*pw2 152) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0153, pw2_0152, pw2_0001, pw2_0000]
  decide
#print axioms p2_d038_s0_flat30
/-- Pinned raw matrix row 214, raw column 20, flat 31. -/
theorem p0_d038_s1_flat31 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 1 (.inr (.inl 0)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw0 154 - 7^(1+1)*pw0 152) - (pw0 2 - 7^(1+1)*pw0 0) = 0
  rw [pw0_0154, pw0_0152, pw0_0002, pw0_0000]
  decide
#print axioms p0_d038_s1_flat31
/-- Pinned raw matrix row 216, raw column 20, flat 31. -/
theorem p2_d038_s1_flat31 :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 38 1 (.inr (.inl 2)) = 0 := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change (pw2 154 - 7^(1+1)*pw2 152) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0154, pw2_0152, pw2_0002, pw2_0000]
  decide
#print axioms p2_d038_s1_flat31
end AspisV8R19.R806Point02SelectedChunk03
