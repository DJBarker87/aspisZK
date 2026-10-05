import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk08
import AspisV8R19.R806Point02SelectedChunk09
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P0StaticChunk04
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk08
open AspisV8R19.R806Point02SelectedChunk09
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p0_d061_s0_flat67 : fixedSourceMatrix (pointPosition 0) (⟨61,by decide⟩ : Fin 222) = 4323 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 61 0 (.inr (.inl 0)) = 4323
  exact p0_d061_s0_flat67
#print axioms static_p0_d061_s0_flat67

theorem static_p0_d061_s2_flat68 : fixedSourceMatrix (pointPosition 0) (⟨62,by decide⟩ : Fin 222) = 227988 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 61 2 (.inr (.inl 0)) = 227988
  exact p0_d061_s2_flat68
#print axioms static_p0_d061_s2_flat68

theorem static_p0_d062_s0_flat69 : fixedSourceMatrix (pointPosition 0) (⟨63,by decide⟩ : Fin 222) = 5274 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 62 0 (.inr (.inl 0)) = 5274
  exact p0_d062_s0_flat69
#print axioms static_p0_d062_s0_flat69

theorem static_p0_d062_s2_flat70 : fixedSourceMatrix (pointPosition 0) (⟨64,by decide⟩ : Fin 222) = 254844 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 62 2 (.inr (.inl 0)) = 254844
  exact p0_d062_s2_flat70
#print axioms static_p0_d062_s2_flat70

theorem static_p0_d063_s0_flat71 : fixedSourceMatrix (pointPosition 0) (⟨65,by decide⟩ : Fin 222) = 1610606082 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 63 0 (.inr (.inl 0)) = 1610606082
  exact p0_d063_s0_flat71
#print axioms static_p0_d063_s0_flat71

theorem static_p0_d027_s2_flat72 : fixedSourceMatrix (pointPosition 0) (⟨220,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 27 2 (.inr (.inl 0)) = 0
  exact p0_d027_s2_flat72
#print axioms static_p0_d027_s2_flat72

theorem static_p0_d047_s2_flat73 : fixedSourceMatrix (pointPosition 0) (⟨221,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 0)) = 0
  exact p0_d047_s2_flat73
#print axioms static_p0_d047_s2_flat73

end
end AspisV8R19.R812SourceBlock06P0StaticChunk04
