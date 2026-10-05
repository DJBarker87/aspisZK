import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk08
import AspisV8R19.R806Point02SelectedChunk09
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2StaticChunk04
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk08
open AspisV8R19.R806Point02SelectedChunk09
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p2_d061_s0_flat67 : fixedSourceMatrix (pointPosition 2) (⟨61,by decide⟩ : Fin 222) = 1441 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 61 0 (.inr (.inl 2)) = 1441
  exact p2_d061_s0_flat67
#print axioms static_p2_d061_s0_flat67

theorem static_p2_d061_s2_flat68 : fixedSourceMatrix (pointPosition 2) (⟨62,by decide⟩ : Fin 222) = 75996 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 61 2 (.inr (.inl 2)) = 75996
  exact p2_d061_s2_flat68
#print axioms static_p2_d061_s2_flat68

theorem static_p2_d062_s0_flat69 : fixedSourceMatrix (pointPosition 2) (⟨63,by decide⟩ : Fin 222) = 1758 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 62 0 (.inr (.inl 2)) = 1758
  exact p2_d062_s0_flat69
#print axioms static_p2_d062_s0_flat69

theorem static_p2_d062_s2_flat70 : fixedSourceMatrix (pointPosition 2) (⟨64,by decide⟩ : Fin 222) = 84948 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 62 2 (.inr (.inl 2)) = 84948
  exact p2_d062_s2_flat70
#print axioms static_p2_d062_s2_flat70

theorem static_p2_d063_s0_flat71 : fixedSourceMatrix (pointPosition 2) (⟨65,by decide⟩ : Fin 222) = 536868694 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 63 0 (.inr (.inl 2)) = 536868694
  exact p2_d063_s0_flat71
#print axioms static_p2_d063_s0_flat71

theorem static_p2_d027_s2_flat72 : fixedSourceMatrix (pointPosition 2) (⟨220,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 27 2 (.inr (.inl 2)) = 0
  exact p2_d027_s2_flat72
#print axioms static_p2_d027_s2_flat72

theorem static_p2_d047_s2_flat73 : fixedSourceMatrix (pointPosition 2) (⟨221,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 2)) = 0
  exact p2_d047_s2_flat73
#print axioms static_p2_d047_s2_flat73

end
end AspisV8R19.R812SourceBlock06P2StaticChunk04
