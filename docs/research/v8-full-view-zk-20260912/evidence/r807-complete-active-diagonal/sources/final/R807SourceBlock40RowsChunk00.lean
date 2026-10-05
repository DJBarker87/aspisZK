import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC40Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk45
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock40RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block40_row00 :
    (fun j : Fin 1 => reorderedSourceMatrix (flatIndex 40 (⟨0, by decide⟩ : Fin 1)) (flatIndex 40 j)) =
      (fun j => R752SCC40Matrix.A_scc (⟨0, by decide⟩ : Fin 1) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨182, by decide⟩ : Fin 214))
    (colOrder (flatIndex 40 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk45.literalSourceMatrix_row958]
  fin_cases j <;> rfl
#print axioms source_block40_row00

end

end AspisV8R19.R807SourceBlock40RowsChunk00
