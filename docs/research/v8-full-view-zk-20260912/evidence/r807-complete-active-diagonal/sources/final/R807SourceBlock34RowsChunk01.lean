import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC34Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk39
import AspisV8R19.R804LiteralSourceRowsChunk40
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock34RowsChunk01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block34_row02 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 34 (⟨2, by decide⟩ : Fin 4)) (flatIndex 34 j)) =
      (fun j => R752SCC34Matrix.A_scc (⟨2, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨160, by decide⟩ : Fin 214))
    (colOrder (flatIndex 34 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk39.literalSourceMatrix_row908]
  fin_cases j <;> rfl
#print axioms source_block34_row02

theorem source_block34_row03 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 34 (⟨3, by decide⟩ : Fin 4)) (flatIndex 34 j)) =
      (fun j => R752SCC34Matrix.A_scc (⟨3, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨161, by decide⟩ : Fin 214))
    (colOrder (flatIndex 34 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk40.literalSourceMatrix_row910]
  fin_cases j <;> rfl
#print axioms source_block34_row03

end

end AspisV8R19.R807SourceBlock34RowsChunk01
