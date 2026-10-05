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
namespace AspisV8R19.R812SourceBlock00Cells03
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem source_cell_3_0 : fixedSourceMatrix (219 : Fin 222) (214 : Fin 222) = 1073740136 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 3 = 1073740136
  exact R810CoefficientCellsChunk01.coeff3_d23_s0
#print axioms source_cell_3_0

theorem source_cell_3_1 : fixedSourceMatrix (219 : Fin 222) (215 : Fin 222) = 1342162795 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 3 = 1342162795
  exact R810CoefficientCellsChunk01.coeff3_d23_s1
#print axioms source_cell_3_1

theorem source_cell_3_2 : fixedSourceMatrix (219 : Fin 222) (216 : Fin 222) = 536774443 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨23,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 3 = 536774443
  exact R810CoefficientCellsChunk01.coeff3_d23_s2
#print axioms source_cell_3_2

theorem source_cell_3_3 : fixedSourceMatrix (219 : Fin 222) (217 : Fin 222) = 9450 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨0,by decide⟩ : Fin 3)) 3 = 9450
  exact R810CoefficientCellsChunk01.coeff3_d24_s0
#print axioms source_cell_3_3

theorem source_cell_3_4 : fixedSourceMatrix (219 : Fin 222) (218 : Fin 222) = 208275 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨1,by decide⟩ : Fin 3)) 3 = 208275
  exact R810CoefficientCellsChunk01.coeff3_d24_s1
#print axioms source_cell_3_4

theorem source_cell_3_5 : fixedSourceMatrix (219 : Fin 222) (219 : Fin 222) = 1337250 := by
  have hp : coefficientPosition (⟨2,by decide⟩ : Fin 5) = (219 : Fin 222) := by decide
  rw [← hp]
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_entry, sourceView_coefficientPosition]
  change rawRelation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 z (indexedDirection 7 (⟨24,by decide⟩ : Fin 255) (⟨2,by decide⟩ : Fin 3)) 3 = 1337250
  exact R810CoefficientCellsChunk01.coeff3_d24_s2
#print axioms source_cell_3_5
end
end AspisV8R19.R812SourceBlock00Cells03
