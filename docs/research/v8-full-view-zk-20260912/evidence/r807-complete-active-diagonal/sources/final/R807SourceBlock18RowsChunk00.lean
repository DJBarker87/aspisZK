import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC18Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk29
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock18RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block18_row00 :
    (fun j : Fin 2 => reorderedSourceMatrix (flatIndex 18 (⟨0, by decide⟩ : Fin 2)) (flatIndex 18 j)) =
      (fun j => R752SCC18Matrix.A_scc (⟨0, by decide⟩ : Fin 2) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨118, by decide⟩ : Fin 214))
    (colOrder (flatIndex 18 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk29.literalSourceMatrix_row365]
  fin_cases j <;> rfl
#print axioms source_block18_row00

theorem source_block18_row01 :
    (fun j : Fin 2 => reorderedSourceMatrix (flatIndex 18 (⟨1, by decide⟩ : Fin 2)) (flatIndex 18 j)) =
      (fun j => R752SCC18Matrix.A_scc (⟨1, by decide⟩ : Fin 2) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨119, by decide⟩ : Fin 214))
    (colOrder (flatIndex 18 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk29.literalSourceMatrix_row367]
  fin_cases j <;> rfl
#print axioms source_block18_row01

end

end AspisV8R19.R807SourceBlock18RowsChunk00
