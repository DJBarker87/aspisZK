import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC26Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk35
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock26RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block26_row00 :
    (fun j : Fin 1 => reorderedSourceMatrix (flatIndex 26 (⟨0, by decide⟩ : Fin 1)) (flatIndex 26 j)) =
      (fun j => R752SCC26Matrix.A_scc (⟨0, by decide⟩ : Fin 1) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨142, by decide⟩ : Fin 214))
    (colOrder (flatIndex 26 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk35.literalSourceMatrix_row755]
  fin_cases j <;> rfl
#print axioms source_block26_row00

end

end AspisV8R19.R807SourceBlock26RowsChunk00
