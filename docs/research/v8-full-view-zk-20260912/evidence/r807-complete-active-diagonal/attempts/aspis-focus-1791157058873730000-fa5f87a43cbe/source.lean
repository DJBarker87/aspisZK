import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC22Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk34
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock22RowsChunk02
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block22_row04 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 22 (⟨4, by decide⟩ : Fin 8)) (flatIndex 22 j)) =
      (fun j => R752SCC22Matrix.A_scc (⟨4, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨138, by decide⟩ : Fin 214))
    (colOrder (flatIndex 22 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk34.literalSourceMatrix_row634]
  fin_cases j <;> rfl
#print axioms source_block22_row04

theorem source_block22_row05 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 22 (⟨5, by decide⟩ : Fin 8)) (flatIndex 22 j)) =
      (fun j => R752SCC22Matrix.A_scc (⟨5, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨139, by decide⟩ : Fin 214))
    (colOrder (flatIndex 22 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk34.literalSourceMatrix_row636]
  fin_cases j <;> rfl
#print axioms source_block22_row05

end

end AspisV8R19.R807SourceBlock22RowsChunk02
