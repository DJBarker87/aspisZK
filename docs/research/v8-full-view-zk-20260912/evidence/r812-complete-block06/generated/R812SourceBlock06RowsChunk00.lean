import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk00

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk00
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local01 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨1, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨1, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨1, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨1, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨1,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row116]
  revert j
  decide
#print axioms source_block06_active_row_local01

theorem source_block06_active_row_local02 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨2, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨2, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨2, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨2, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨2,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row118]
  revert j
  decide
#print axioms source_block06_active_row_local02

theorem source_block06_active_row_local03 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨3, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨3, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨3, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨3, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨3,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row120]
  revert j
  decide
#print axioms source_block06_active_row_local03

theorem source_block06_active_row_local04 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨4, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨4, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨4, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨4, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨4,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row122]
  revert j
  decide
#print axioms source_block06_active_row_local04

end
end AspisV8R19.R812SourceBlock06RowsChunk00
