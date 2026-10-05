import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SCC02Matrix
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRowsChunk07
import AspisV8R19.R804LiteralSourceRowsChunk08
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R807SourceBlock01Binding
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R807SourceBlock02Binding
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R724BlockOrderMaps
noncomputable section

theorem source_block02_eq_certificate : diagonalSourceBlock 2 = R752SCC02Matrix.A_scc := by
  ext i j
  fin_cases i
  · change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨31, by decide⟩ : Fin 214))
      (colOrder (flatIndex 2 j)) = _
    rw [AspisV8R19.R804LiteralSourceRowsChunk07.literalSourceMatrix_row176]
    fin_cases j <;> rfl
  · change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨32, by decide⟩ : Fin 214))
      (colOrder (flatIndex 2 j)) = _
    rw [AspisV8R19.R804LiteralSourceRowsChunk07.literalSourceMatrix_row178]
    fin_cases j <;> rfl
  · change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨33, by decide⟩ : Fin 214))
      (colOrder (flatIndex 2 j)) = _
    rw [AspisV8R19.R804LiteralSourceRowsChunk08.literalSourceMatrix_row180]
    fin_cases j <;> rfl
#print axioms source_block02_eq_certificate
end

end AspisV8R19.R807SourceBlock02Binding
