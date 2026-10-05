import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk13
import AspisV8R19.R804LiteralSourceRowsChunk14

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06RowsChunk06
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRowsChunk13
open AspisV8R19.R804LiteralSourceRowsChunk14
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_active_row_local25 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨25, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨25, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨25, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨25, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨54, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨54,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row230]
  revert j
  decide
#print axioms source_block06_active_row_local25

theorem source_block06_active_row_local26 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨26, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨26, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨26, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨26, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨55, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨55,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row232]
  revert j
  decide
#print axioms source_block06_active_row_local26

theorem source_block06_active_row_local27 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨27, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨27, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨27, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨27, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨56, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨56,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row234]
  revert j
  decide
#print axioms source_block06_active_row_local27

theorem source_block06_active_row_local28 (j : Fin 39) :
    diagonalSourceBlock 6 (⟨28, by decide⟩ : Fin (blockSize 6)) j =
      R747JointBlock39Preflight.A (⟨28, by decide⟩ : Fin 39) j := by
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨28, by decide⟩ : Fin (blockSize 6))))
    (colOrder (flatIndex 6 j)) = _
  have hrow : rowOrder (flatIndex 6 (⟨28, by decide⟩ : Fin (blockSize 6))) =
      activePosition (⟨57, by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨57,by decide⟩ : Fin 214))
    (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row236]
  revert j
  decide
#print axioms source_block06_active_row_local28

end
end AspisV8R19.R812SourceBlock06RowsChunk06
