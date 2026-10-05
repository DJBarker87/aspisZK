import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC23Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk36
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock23RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block23_row00 :
    (fun j : Fin 2 => reorderedSourceMatrix (flatIndex 23 (⟨0, by decide⟩ : Fin 2)) (flatIndex 23 j)) =
      (fun j => R752SCC23Matrix.A_scc (⟨0, by decide⟩ : Fin 2) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨147, by decide⟩ : Fin 214))
    (colOrder (flatIndex 23 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk36.literalSourceMatrix_row765]
  fin_cases j <;> rfl
#print axioms source_block23_row00

theorem source_block23_row01 :
    (fun j : Fin 2 => reorderedSourceMatrix (flatIndex 23 (⟨1, by decide⟩ : Fin 2)) (flatIndex 23 j)) =
      (fun j => R752SCC23Matrix.A_scc (⟨1, by decide⟩ : Fin 2) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨148, by decide⟩ : Fin 214))
    (colOrder (flatIndex 23 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk36.literalSourceMatrix_row766]
  fin_cases j <;> rfl
#print axioms source_block23_row01

end

end AspisV8R19.R807SourceBlock23RowsChunk00
