import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk08
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812Row36Inspect
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R801LiteralActiveEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R804LiteralSourceRowsChunk08
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
example (j : Fin 39) : diagonalSourceBlock 6 (⟨36,by decide⟩ : Fin (blockSize 6)) j = R747JointBlock39Preflight.A (⟨36,by decide⟩ : Fin39) j := by
  unfold diagonalSourceBlock reorderedSourceMatrix
  have hrow : rowOrder (flatIndex 6 (⟨36,by decide⟩ : Fin (blockSize 6))) = activePosition (⟨36,by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected kappaSelected tauSelected z) (activePosition (⟨36,by decide⟩ : Fin 214)) (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row194]
  revert j
  decide
end
end AspisV8R19.R812Row36Inspect
