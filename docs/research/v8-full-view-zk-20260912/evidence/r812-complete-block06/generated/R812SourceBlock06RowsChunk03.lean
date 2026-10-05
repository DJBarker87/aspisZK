import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk10
import AspisV8R19.R804LiteralSourceRowsChunk11

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk03
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk10
open AspisV8R19.R804LiteralSourceRowsChunk11
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local13 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨13, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨13, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨13, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨42, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨42,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row206]
  revert j
  decide
#print axioms source_block06_active_row_local13

theorem source_block06_active_row_local14 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨14, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨14, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨14, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨43, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨43,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row208]
  revert j
  decide
#print axioms source_block06_active_row_local14

theorem source_block06_active_row_local15 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨15, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨15, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨15, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨44, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨44,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row210]
  revert j
  decide
#print axioms source_block06_active_row_local15

theorem source_block06_active_row_local16 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨16, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨16, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨16, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨45, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨45,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row212]
  revert j
  decide
#print axioms source_block06_active_row_local16

end
end AspisV8R19.R812SourceBlock06RowsChunk03
