import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk01P2
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R780Point02WeightPrototype
open AspisV8R19.R780Point02WeightChunk00P2 AspisV8R19.R780Point02WeightChunk01P2
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R806InspectP2
abbrev M := ZMod 2147483647
example : sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 23 0 (.inr (.inl 2)) = 0 := by
  unfold sparseObservation
  change (pw2 93 - 7^(0+1)*pw2 92) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0093, pw2_0092, pw2_0001, pw2_0000]
  trace_state
  sorry
end AspisV8R19.R806InspectP2
