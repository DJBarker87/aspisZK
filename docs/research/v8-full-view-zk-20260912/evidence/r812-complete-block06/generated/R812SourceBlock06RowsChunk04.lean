import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk11
import AspisV8R19.R804LiteralSourceRowsChunk12

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk04
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk11
open AspisV8R19.R804LiteralSourceRowsChunk12
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local17 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨17, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨17, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨17, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨46, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨46,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row214]
  revert j
  decide
#print axioms source_block06_active_row_local17

theorem source_block06_active_row_local18 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨18, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨18, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨18, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨47, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨47,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row216]
  revert j
  decide
#print axioms source_block06_active_row_local18

theorem source_block06_active_row_local19 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨19, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨19, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨19, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨48, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨48,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row218]
  revert j
  decide
#print axioms source_block06_active_row_local19

theorem source_block06_active_row_local20 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨20, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨20, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨20, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨49, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨49,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row220]
  revert j
  decide
#print axioms source_block06_active_row_local20

end
end AspisV8R19.R812SourceBlock06RowsChunk04
