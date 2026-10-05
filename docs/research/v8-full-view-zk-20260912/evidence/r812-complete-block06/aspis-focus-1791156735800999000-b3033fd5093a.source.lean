import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk09
import AspisV8R19.R804LiteralSourceRowsChunk10

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk02
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk09
open AspisV8R19.R804LiteralSourceRowsChunk10
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local09 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨9, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨9, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨9, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨9, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨38, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨38,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row198]
  revert j
  decide
#print axioms source_block06_active_row_local09

theorem source_block06_active_row_local10 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨10, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨10, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨10, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨10, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨39, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨39,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row200]
  revert j
  decide
#print axioms source_block06_active_row_local10

theorem source_block06_active_row_local11 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨11, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨11, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨11, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨11, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨40, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨40,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row202]
  revert j
  decide
#print axioms source_block06_active_row_local11

theorem source_block06_active_row_local12 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨12, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨12, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨12, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨12, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨41, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨41,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row204]
  revert j
  decide
#print axioms source_block06_active_row_local12

end
end AspisV8R19.R812SourceBlock06RowsChunk02
