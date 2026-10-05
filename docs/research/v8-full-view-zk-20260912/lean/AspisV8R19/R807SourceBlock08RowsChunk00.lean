import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC08Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk20
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock08RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block08_row00 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 8 (⟨0, by decide⟩ : Fin 8)) (flatIndex 8 j)) =
      (fun j => R752SCC08Matrix.A_scc (⟨0, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨82, by decide⟩ : Fin 214))
    (colOrder (flatIndex 8 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk20.literalSourceMatrix_row289]
  fin_cases j <;> rfl
#print axioms source_block08_row00

theorem source_block08_row01 :
    (fun j : Fin 8 => reorderedSourceMatrix (flatIndex 8 (⟨1, by decide⟩ : Fin 8)) (flatIndex 8 j)) =
      (fun j => R752SCC08Matrix.A_scc (⟨1, by decide⟩ : Fin 8) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨83, by decide⟩ : Fin 214))
    (colOrder (flatIndex 8 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk20.literalSourceMatrix_row291]
  fin_cases j <;> rfl
#print axioms source_block08_row01

end

end AspisV8R19.R807SourceBlock08RowsChunk00
