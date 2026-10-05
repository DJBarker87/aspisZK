import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2Static00
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding AspisV8R19.R806Point02SelectedChunk04
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩
theorem p2_static00 : fixedSourceMatrix (pointPosition 2) (⟨0,by decide⟩ : Fin 222) = 0 := by
 unfold fixedSourceMatrix
 rw [literalSourceMatrix_point_entry]
 change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 2)) = 0
 exact p2_d028_s1_flat35
#print axioms p2_static00
end
end AspisV8R19.R812SourceBlock06P2Static00
