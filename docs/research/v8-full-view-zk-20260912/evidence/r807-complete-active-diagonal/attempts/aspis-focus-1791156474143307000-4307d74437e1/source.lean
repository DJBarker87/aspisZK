import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC03Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk06
import AspisV8R19.R804LiteralSourceRowsChunk07
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock03RowsChunk02
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block03_row05 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 3 (⟨5, by decide⟩ : Fin 8)) (flatIndex 3 j)) =
      (fun j => R752SCC03Matrix.A_scc (⟨5, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨28, by decide⟩ : Fin 214))
    (colOrder (flatIndex 3 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk06.literalSourceMatrix_row170]
  fin_cases j <;> rfl
#print axioms source_block03_row05

theorem source_block03_row06 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 3 (⟨6, by decide⟩ : Fin 8)) (flatIndex 3 j)) =
      (fun j => R752SCC03Matrix.A_scc (⟨6, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨29, by decide⟩ : Fin 214))
    (colOrder (flatIndex 3 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk07.literalSourceMatrix_row172]
  fin_cases j <;> rfl
#print axioms source_block03_row06

end

end AspisV8R19.R807SourceBlock03RowsChunk02
