import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk01
import AspisV8R19.R804LiteralSourceRowsChunk08
import AspisV8R19.R804LiteralSourceRowsChunk09

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk01
open AspisV8R19.R804LiteralSourceRowsChunk08
open AspisV8R19.R804LiteralSourceRowsChunk09
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local05 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨5, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨5, by decide⟩ : Fin 39) j := by
  unfold diagonalSourceBlock reorderedSourceMatrix
  have hrow : rowOrder (flatIndex 6 (⟨5, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨5, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨5,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row124]
  revert j
  decide
#print axioms source_block06_active_row_local05

theorem source_block06_active_row_local06 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨6, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨6, by decide⟩ : Fin 39) j := by
  unfold diagonalSourceBlock reorderedSourceMatrix
  have hrow : rowOrder (flatIndex 6 (⟨6, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨6, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨6,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row126]
  revert j
  decide
#print axioms source_block06_active_row_local06

theorem source_block06_active_row_local07 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨7, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨7, by decide⟩ : Fin 39) j := by
  unfold diagonalSourceBlock reorderedSourceMatrix
  have hrow : rowOrder (flatIndex 6 (⟨7, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨36, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨36,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row194]
  revert j
  decide
#print axioms source_block06_active_row_local07

theorem source_block06_active_row_local08 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨8, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨8, by decide⟩ : Fin 39) j := by
  unfold diagonalSourceBlock reorderedSourceMatrix
  have hrow : rowOrder (flatIndex 6 (⟨8, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨37, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨37,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row196]
  revert j
  decide
#print axioms source_block06_active_row_local08

end
end AspisV8R19.R812SourceBlock06RowsChunk01
