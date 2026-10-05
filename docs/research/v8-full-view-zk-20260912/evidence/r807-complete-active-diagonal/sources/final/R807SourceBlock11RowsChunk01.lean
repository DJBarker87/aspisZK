import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC11Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk28
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock11RowsChunk01
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block11_row02 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 11 (⟨2, by decide⟩ : Fin 4)) (flatIndex 11 j)) =
      (fun j => R752SCC11Matrix.A_scc (⟨2, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨115, by decide⟩ : Fin 214))
    (colOrder (flatIndex 11 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk28.literalSourceMatrix_row357]
  fin_cases j <;> rfl
#print axioms source_block11_row02

theorem source_block11_row03 :
    (fun j : Fin 4 => reorderedSourceMatrix (flatIndex 11 (⟨3, by decide⟩ : Fin 4)) (flatIndex 11 j)) =
      (fun j => R752SCC11Matrix.A_scc (⟨3, by decide⟩ : Fin 4) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨116, by decide⟩ : Fin 214))
    (colOrder (flatIndex 11 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk28.literalSourceMatrix_row359]
  fin_cases j <;> rfl
#print axioms source_block11_row03

end

end AspisV8R19.R807SourceBlock11RowsChunk01
