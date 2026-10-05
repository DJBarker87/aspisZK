import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk14
import AspisV8R19.R804LiteralSourceRowsChunk15

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk07
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk14
open AspisV8R19.R804LiteralSourceRowsChunk15
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local29 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨29, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨29, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨29, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨58, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨58,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row238]
  revert j
  decide
#print axioms source_block06_active_row_local29

theorem source_block06_active_row_local30 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨30, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨30, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨30, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨59, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨59,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row240]
  revert j
  decide
#print axioms source_block06_active_row_local30

theorem source_block06_active_row_local31 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨31, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨31, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨31, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨60, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨60,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row243]
  revert j
  decide
#print axioms source_block06_active_row_local31

theorem source_block06_active_row_local32 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨32, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨32, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨32, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨61, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨61,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row245]
  revert j
  decide
#print axioms source_block06_active_row_local32

end
end AspisV8R19.R812SourceBlock06RowsChunk07
