import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2Entry00
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk04
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
theorem source_block06_p2_entry00 :
  diagonalSourceBlock 6 (⟨37,by decide⟩ : Fin (blockSize 6)) (⟨0,by decide⟩ : Fin 39) =
    R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨0,by decide⟩ : Fin 39) := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨37,by decide⟩ : Fin (blockSize 6))) = pointPosition (⟨2,by decide⟩ : Fin 3) := by decide
  rw [hrow]
  change literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨0,by decide⟩ : Fin 39))) = _
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 2)) = _
  exact p2_d028_s1_flat35
#print axioms source_block06_p2_entry00
end
end AspisV8R19.R812SourceBlock06P2Entry00
