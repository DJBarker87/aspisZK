import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P0StaticLowChunk04
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk04
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p0_d039_s0_flat32 : fixedSourceMatrix (pointPosition 0) (⟨21,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 39 0 (.inr (.inl 0)) = 0
  exact p0_d039_s0_flat32
#print axioms static_p0_d039_s0_flat32

theorem static_p0_d039_s1_flat33 : fixedSourceMatrix (pointPosition 0) (⟨22,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 39 1 (.inr (.inl 0)) = 0
  exact p0_d039_s1_flat33
#print axioms static_p0_d039_s1_flat33

theorem static_p0_d047_s1_flat34 : fixedSourceMatrix (pointPosition 0) (⟨35,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 47 1 (.inr (.inl 0)) = 0
  exact p0_d047_s1_flat34
#print axioms static_p0_d047_s1_flat34

end
end AspisV8R19.R812SourceBlock06P0StaticLowChunk04
