import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC08Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk21
import AspisV8R19.R804LiteralSourceRowsChunk22
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock08RowsChunk03
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block08_row06 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 8 (⟨6, by decide⟩ : Fin 8)) (flatIndex 8 j)) =
      (fun j => R752SCC08Matrix.A_scc (⟨6, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨88, by decide⟩ : Fin 214))
    (colOrder (flatIndex 8 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk21.literalSourceMatrix_row301]
  fin_cases j <;> rfl
#print axioms source_block08_row06

theorem source_block08_row07 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 8 (⟨7, by decide⟩ : Fin 8)) (flatIndex 8 j)) =
      (fun j => R752SCC08Matrix.A_scc (⟨7, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨89, by decide⟩ : Fin 214))
    (colOrder (flatIndex 8 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk22.literalSourceMatrix_row303]
  fin_cases j <;> rfl
#print axioms source_block08_row07

end

end AspisV8R19.R807SourceBlock08RowsChunk03
