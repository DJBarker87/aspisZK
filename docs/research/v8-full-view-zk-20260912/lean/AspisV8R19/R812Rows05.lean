import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk12
import AspisV8R19.R804LiteralSourceRowsChunk13

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk05
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk12
open AspisV8R19.R804LiteralSourceRowsChunk13
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local21 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨21, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨21, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨21, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨21, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨50, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨50,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row222]
  revert j
  decide
#print axioms source_block06_active_row_local21

theorem source_block06_active_row_local22 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨22, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨22, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨22, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨22, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨51, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨51,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row224]
  revert j
  decide
#print axioms source_block06_active_row_local22

theorem source_block06_active_row_local23 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨23, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨23, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨23, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨23, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨52, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨52,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row226]
  revert j
  decide
#print axioms source_block06_active_row_local23

theorem source_block06_active_row_local24 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨24, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨24, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨24, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨24, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨53, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨53,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row228]
  revert j
  decide
#print axioms source_block06_active_row_local24

end
end AspisV8R19.R812SourceBlock06RowsChunk05
