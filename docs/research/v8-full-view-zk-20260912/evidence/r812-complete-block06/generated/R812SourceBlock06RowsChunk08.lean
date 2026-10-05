import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk15
import AspisV8R19.R804LiteralSourceRowsChunk16

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk08
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk15
open AspisV8R19.R804LiteralSourceRowsChunk16
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local33 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨33, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨33, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨33, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨62, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨62,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row247]
  revert j
  decide
#print axioms source_block06_active_row_local33

theorem source_block06_active_row_local34 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨34, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨34, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨34, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨63, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨63,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row249]
  revert j
  decide
#print axioms source_block06_active_row_local34

theorem source_block06_active_row_local35 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨35, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨35, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨35, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨64, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨64,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row251]
  revert j
  decide
#print axioms source_block06_active_row_local35

theorem source_block06_active_row_local36 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨36, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨36, by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨36, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨65, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨65,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row253]
  revert j
  decide
#print axioms source_block06_active_row_local36

end
end AspisV8R19.R812SourceBlock06RowsChunk08
