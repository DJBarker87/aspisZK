import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R769Point1SelectedChunk06

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812Block00CellBridge
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R743JointSparseEntryBinding
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem source_point_cell00 : fixedSourceMatrix (pointPosition 1) (⟨214,by decide⟩ : Fin 222) = 45 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 23 0 (.inr (.inl 1)) = 45
  exact R769Point1SelectedChunk06.point1_d023_s0

#print axioms source_point_cell00
end
end AspisV8R19.R812Block00CellBridge
