import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R724BlockOrderMaps
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2Leaf00
open AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk04
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
theorem p2_leaf00 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨0,by decide⟩ : Fin 39))) = 0 := by
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 2)) = _
  exact p2_d028_s1_flat35
#print axioms p2_leaf00
end
end AspisV8R19.R812SourceBlock06P2Leaf00
