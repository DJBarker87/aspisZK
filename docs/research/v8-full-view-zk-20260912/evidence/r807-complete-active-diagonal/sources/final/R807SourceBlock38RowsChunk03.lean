import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC38Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk51
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock38RowsChunk03
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block38_row06 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 38 (⟨6, by decide⟩ : Fin 8)) (flatIndex 38 j)) =
      (fun j => R752SCC38Matrix.A_scc (⟨6, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨205, by decide⟩ : Fin 214))
    (colOrder (flatIndex 38 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk51.literalSourceMatrix_row1004]
  fin_cases j <;> rfl
#print axioms source_block38_row06

theorem source_block38_row07 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 38 (⟨7, by decide⟩ : Fin 8)) (flatIndex 38 j)) =
      (fun j => R752SCC38Matrix.A_scc (⟨7, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨206, by decide⟩ : Fin 214))
    (colOrder (flatIndex 38 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk51.literalSourceMatrix_row1006]
  fin_cases j <;> rfl
#print axioms source_block38_row07

end

end AspisV8R19.R807SourceBlock38RowsChunk03
