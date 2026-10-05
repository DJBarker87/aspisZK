import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC36Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk52
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock36RowsChunk00
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block36_row00 :
    (fun j : Fin 3 => reorderedSourceMatrix (flatIndex 36 (⟨0, by decide⟩ : Fin 3)) (flatIndex 36 j)) =
      (fun j => R752SCC36Matrix.A_scc (⟨0, by decide⟩ : Fin 3) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨211, by decide⟩ : Fin 214))
    (colOrder (flatIndex 36 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk52.literalSourceMatrix_row1017]
  fin_cases j <;> rfl
#print axioms source_block36_row00

theorem source_block36_row01 :
    (fun j : Fin 3 => reorderedSourceMatrix (flatIndex 36 (⟨1, by decide⟩ : Fin 3)) (flatIndex 36 j)) =
      (fun j => R752SCC36Matrix.A_scc (⟨1, by decide⟩ : Fin 3) j) := by
  funext j
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
    kappaSelected tauSelected z) (activePosition (⟨212, by decide⟩ : Fin 214))
    (colOrder (flatIndex 36 j)) = _
  rw [AspisV8R19.R804LiteralSourceRowsChunk52.literalSourceMatrix_row1019]
  fin_cases j <;> rfl
#print axioms source_block36_row01

end

end AspisV8R19.R807SourceBlock36RowsChunk00
