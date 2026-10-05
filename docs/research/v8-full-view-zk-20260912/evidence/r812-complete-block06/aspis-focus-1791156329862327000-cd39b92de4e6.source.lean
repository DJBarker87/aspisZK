import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R810CoefficientCellPrototype
import AspisV8R19.R810CoefficientCellsChunk00
import AspisV8R19.R810CoefficientCellsChunk01
import AspisV8R19.R810CoefficientCellsChunk02
import AspisV8R19.R769Point1SelectedChunk06
import AspisV8R19.R752SCC00Inverse

set_option autoImplicit false
set_option maxRecDepth 32768
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R803LiteralSupplementaryEntries
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
namespace AspisV8R19.R812SourceBlock00Row00
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem source_block00_row00 : (diagonalSourceBlock 0) (⟨0,by decide⟩) = R752SCC00Matrix.A_scc (⟨0,by decide⟩) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (pointPosition 1) (colOrder (flatIndex 0 j)) = _
  rw [literalSourceMatrix_point_entry]
  fin_cases j
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 23 0 (.inr (.inl 1)) = 45
    exact R769Point1SelectedChunk06.point1_d023_s0
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 23 1 (.inr (.inl 1)) = 45
    exact R769Point1SelectedChunk06.point1_d023_s1
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 23 2 (.inr (.inl 1)) = 1073741711
    exact R769Point1SelectedChunk06.point1_d023_s2
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 24 0 (.inr (.inl 1)) = 2147483527
    exact R769Point1SelectedChunk06.point1_d024_s0
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 24 1 (.inr (.inl 1)) = 672
    exact R769Point1SelectedChunk06.point1_d024_s1
  · change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 24 2 (.inr (.inl 1)) = 27444
    exact R769Point1SelectedChunk06.point1_d024_s2
#print axioms source_block00_row00
end
end AspisV8R19.R812SourceBlock00Row00
