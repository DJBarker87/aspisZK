import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC12Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk24
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock12RowsChunk02
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block12_row02 :
    (fun j : Fin 16 => reorderedSourceMatrix (flatIndex 12 (⟨2, by decide⟩ : Fin 16)) (flatIndex 12 j)) =
      (fun j => R752SCC12Matrix.A_scc (⟨2, by decide⟩ : Fin 16) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨99, by decide⟩ : Fin 214))
    (colOrder (flatIndex 12 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk24.literalSourceMatrix_row325]
  fin_cases j <;> rfl
#print axioms source_block12_row02

end

end AspisV8R19.R807SourceBlock12RowsChunk02
