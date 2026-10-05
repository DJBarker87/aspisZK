import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R804LiteralSourceRow114
import AspisV8R19.R804LiteralSourceRowsChunk14
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812Row31Simp
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R801LiteralActiveEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R804LiteralSourceRowsChunk14
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
example (j : Fin 39) : diagonalSourceBlock 6 (⟨31,by decide⟩ : Fin (blockSize 6)) j = R747JointBlock39Preflight.A (⟨31,by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨31,by decide⟩ : Fin (blockSize 6))) = activePosition (⟨60,by decide⟩ : Fin 214) := by decide
  rw [hrow]
  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected kappaSelected tauSelected z) (activePosition (⟨60,by decide⟩ : Fin 214)) (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_row243]
  revert j
  decide
#print axioms this
end
end AspisV8R19.R812Row31Simp
