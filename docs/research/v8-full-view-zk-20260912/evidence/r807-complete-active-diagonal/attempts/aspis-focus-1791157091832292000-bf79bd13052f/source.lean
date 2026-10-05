import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC27Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk38
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock27RowsChunk01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block27_row02 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 27 (⟨2, by decide⟩ : Fin 4)) (flatIndex 27 j)) =
      (fun j => R752SCC27Matrix.A_scc (⟨2, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨154, by decide⟩ : Fin 214))
    (colOrder (flatIndex 27 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk38.literalSourceMatrix_row892]
  fin_cases j <;> rfl
#print axioms source_block27_row02

theorem source_block27_row03 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 27 (⟨3, by decide⟩ : Fin 4)) (flatIndex 27 j)) =
      (fun j => R752SCC27Matrix.A_scc (⟨3, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨155, by decide⟩ : Fin 214))
    (colOrder (flatIndex 27 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk38.literalSourceMatrix_row894]
  fin_cases j <;> rfl
#print axioms source_block27_row03

end

end AspisV8R19.R807SourceBlock27RowsChunk01
